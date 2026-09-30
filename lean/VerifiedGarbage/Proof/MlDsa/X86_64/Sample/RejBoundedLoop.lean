import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttLoop
import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejBounded
import VerifiedGarbage.Proof.MlDsa.Sample.RejBounded

/-!
# ML-DSA on x86-64: the loop of `vg_mldsa_rej_bounded_poly`

Untrusted: everything here is checked by Lean. The coefficient of an
accepted half-byte, computed without a branch (`rbVal`), is the one of
`CoeffFromHalfByte`, modulo `q` (`rbF_eq`, by evaluation on the 16
half-bytes); so a try does what `hbTry` does (`rbTry_ok`), and an
iteration what `rbStep` does (`rbBody_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q ofInt coeffFromHalfByte)

/-! ## The coefficient of a half-byte -/

/-- `x - s` if `s ≤ x`, as `csub s` computes it. -/
def csubF (s x : BitVec 32) : BitVec 32 :=
  x - s + (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (x.toNat < s.toNat))) &&& s)

/-- `(η - x) mod q`, as `etaSub η` computes it. -/
def etaF (η x : BitVec 32) : BitVec 32 :=
  η - x + (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (η.toNat < x.toNat))) &&& qImm)

/-- What `rbVal η` computes of the half-byte `x`. -/
def rbF : Nat → BitVec 32 → BitVec 32
  | 2, x => etaF 2 (csubF 5 (csubF 10 x))
  | _, x => etaF 4 x

/-- The half-bytes `CoeffFromHalfByte` accepts: those less than this. -/
def rbB (η : Nat) : Nat := if η = 2 then 15 else 9

/-- The coefficient of an accepted half-byte. -/
def rbC (η b : Nat) : Int := if η = 2 then 2 - (b % 5 : Nat) else 4 - b

theorem coeffFromHalfByte_eq {η : Nat} (hη : η = 2 ∨ η = 4) (b : Nat) :
    coeffFromHalfByte η b = if b < rbB η then some (rbC η b) else none := by
  rcases hη with rfl | rfl <;> simp [coeffFromHalfByte, rbB, rbC]

theorem rbF_eq2 : ∀ b < 15, rbF 2 (BitVec.ofNat 32 b) = zw (ofInt (rbC 2 b)) := by decide

theorem rbF_eq4 : ∀ b < 9, rbF 4 (BitVec.ofNat 32 b) = zw (ofInt (rbC 4 b)) := by decide

theorem rbF_eq {η : Nat} (hη : η = 2 ∨ η = 4) {b : Nat} (hb : b < rbB η) :
    rbF η (BitVec.ofNat 32 b) = zw (ofInt (rbC η b)) := by
  rcases hη with rfl | rfl
  · exact rbF_eq2 b hb
  · exact rbF_eq4 b hb

theorem rbBound_toNat {η : Nat} (hη : η = 2 ∨ η = 4) : (rbBound η).toNat = rbB η := by
  rcases hη with rfl | rfl <;> rfl

theorem hbTry_eq {η : Nat} (hη : η = 2 ∨ η = 4) (L : List Zq) (b : Nat) :
    hbTry η L b = if b < rbB η then L ++ [ofInt (rbC η b)] else L := by
  unfold hbTry
  rw [coeffFromHalfByte_eq hη]
  by_cases h : b < rbB η <;> simp [h]

theorem rbVal_ok {η : Nat} (hη : η = 2 ∨ η = 4) (s : State) :
    WP isa (.block (rbVal η)) s fun s' =>
      (s'.gpr .r8 = BitVec.setWidth 64 (rbF η ((s.gpr .rdx).setWidth 32)) ∧ s'.mem = s.mem) ∧
        Keep [.rdx, .r8] s s' := by
  rcases hη with rfl | rfl
  · refine WP.keep _ ?_ (by decide)
    simp only [rbVal, csub, etaSub, List.cons_append, List.nil_append]
    xrun
    all_goals rfl
  · refine WP.keep _ ?_ (by decide)
    simp only [rbVal, etaSub]
    xrun
    all_goals rfl

/-! ## A try -/

theorem rbCmp_ok {η : Nat} (hη : η = 2 ∨ η = 4) (s : State) :
    WP isa (.block [.alu32 .cmp .rdx (.imm (rbBound η))]) s fun s' =>
      s'.cf = some (decide (((s.gpr .rdx).setWidth 32).toNat < rbB η)) ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  xrun [rbBound_toNat hη]

/-- Store the coefficient of the half-byte `b` in `rdx` if it is accepted. -/
theorem rbTry_ok {η : Nat} (hη : η = 2 ∨ η = 4) (s : State) {aP : Addr} {L : List Zq} (h : TryPre s aP L)
    {b : Nat} (hb : b < 16) (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 b) :
    WP isa (rbTry η) s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (hbTry η L b).length ∧ Stored s'.mem aP (hbTry η L b) ∧
        Frame [pR aP] s.mem s'.mem ∧ Keep [.rdx, .r8, .rdi] s s' := by
  have hbn : ((s.gpr .rdx).setWidth 32).toNat = b := by rw [hdx, BitVec.toNat_ofNat]; omega
  refine WP.seq (WP.mono (rbCmp_ok hη s) fun s1 ⟨hc, hm, hg, hrd, hwr⟩ => ?_)
  have k1 : Keep [] s s1 := ⟨fun r _ => by rw [hg], hrd, hwr⟩
  rw [hbn] at hc
  rw [hbTry_eq hη]
  refine WP.ite (decide (b < rbB η)) hc (fun hbb => ?_) (fun hbb => ?_)
  · simp only [decide_eq_true_eq] at hbb
    rw [ifT hbb, WP.block_append_iff]
    refine WP.mono (rbVal_ok hη s1) fun s2 ⟨⟨h8, hm2⟩, k2⟩ => ?_
    have hv : rbF η ((s1.gpr .rdx).setWidth 32) = zw (ofInt (rbC η b)) := by rw [hg, hdx, rbF_eq hη hbb]
    refine WP.mono (store_next (s := s2) (aP := aP) (by rw [k2.gpr (by decide), hg, h.rbp])
      (by rw [k2.gpr (by decide), hg, h.rdi]) h.len (by rw [k2.2.2, hwr]; exact h.wr)
      (by rw [hm2, hm]; exact h.st) .r8 (v := zw (ofInt (rbC η b))) (by rw [h8, sw32_64, hv])
      (by rw [zw_toNat]; exact (ofInt (rbC η b)).isLt)) fun s3 ⟨hdi, hst, hf, k3⟩ => ?_
    rw [ofNat_zw] at hdi hst
    exact ⟨hdi, hst, by rw [← hm, ← hm2]; exact hf, ((k1.trans k2).trans k3).mono (by simp)⟩
  · simp only [decide_eq_false_iff_not] at hbb
    rw [ifF hbb]
    exact WP.block_nil ⟨by rw [hg, h.rdi], by rw [hm]; exact h.st, by rw [hm]; exact Frame.refl _ _,
      k1.mono (by simp)⟩

/-! ## An iteration -/

theorem rbLoad_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1) :
    WP isa (.block rbLoad) s fun s' =>
      (s'.gpr .rax = BitVec.setWidth 64 (s.mem (s.gpr .rsi)) ∧
        (s'.gpr .rdx).setWidth 32 = BitVec.ofNat 32 ((s.mem (s.gpr .rsi)).toNat % 16) ∧
        s'.cf = some (decide ((s.gpr .rdi).toNat < 256)) ∧ s'.mem = s.mem ∧ s'.gpr .rdi = s.gpr .rdi) ∧
      Keep [.rax, .rdx, .rdi] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold rbLoad
  xrun [h0, sx256, show (256 : BitVec 64).toNat = 256 from rfl]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, bw32, show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := _ % 16) (by omega)]

theorem rbHi_ok (s : State) {z : Byte} (hax : s.gpr .rax = BitVec.setWidth 64 z) :
    WP isa (.block rbHi) s fun s' =>
      ((s'.gpr .rdx).setWidth 32 = BitVec.ofNat 32 (z.toNat / 16) ∧
        s'.cf = some (decide ((s.gpr .rdi).toNat < 256)) ∧ s'.mem = s.mem ∧ s'.gpr .rdi = s.gpr .rdi) ∧
      Keep [.rax, .rdx, .rdi] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold rbHi
  xrun [hax, sx256, show (256 : BitVec 64).toNat = 256 from rfl]
  apply BitVec.eq_of_toNat_eq
  rw [shr_toNat, bw32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := _ / 16) (by have := z.isLt; omega)]

/-- The coefficients after the second try, if `j < 256`. -/
def rbMid2 (η : Nat) (L : List Zq) (b : Nat) : List Zq := if L.length < 256 then hbTry η L b else L

/-- The coefficients after an iteration, from the byte `z`. -/
theorem rbStep_eq (η : Nat) (L : List Zq) (z : Byte) :
    rbStep η L z = if L.length < 256 then rbMid2 η (hbTry η L (z.toNat % 16)) (z.toNat / 16) else L := by
  rw [rbStep, rbMid2]

theorem hbTry_length_le {η : Nat} {L : List Zq} (hL : L.length < 256) (b : Nat) : (hbTry η L b).length ≤ 256 := by
  rw [hbTry_length]; have := halfByteOk_le η b; omega

/-- The second try, if `j < 256`. -/
theorem rbMid2_ok {η : Nat} (hη : η = 2 ∨ η = 4) (s : State) {aP : Addr} {L : List Zq} (hbp : s.gpr .rbp = aP)
    (hdi : s.gpr .rdi = BitVec.ofNat 64 L.length) (hL : L.length ≤ 256) (hw : pR aP ∈ s.wr)
    (hst : Stored s.mem aP L) (hcf : s.cf = some (decide ((s.gpr .rdi).toNat < 256))) {b : Nat} (hb : b < 16)
    (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 b) :
    WP isa (.ite .b (rbTry η) (.block [])) s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (rbMid2 η L b).length ∧ Stored s'.mem aP (rbMid2 η L b) ∧
        Frame [pR aP] s.mem s'.mem ∧ Keep [.rdx, .r8, .rdi] s s' := by
  have hl : (s.gpr .rdi).toNat = L.length := by rw [hdi, ofNat64_toNat (by omega)]
  refine WP.ite (decide (L.length < 256)) (by rw [← hl]; exact hcf) (fun hbb => ?_) (fun hbb => ?_)
  · simp only [decide_eq_true_eq] at hbb
    rw [rbMid2, ifT hbb]
    exact rbTry_ok hη s ⟨hbp, hdi, hbb, hw, hst⟩ hb hdx
  · simp only [decide_eq_false_iff_not] at hbb
    rw [rbMid2, ifF hbb]
    exact WP.block_nil ⟨hdi, hst, Frame.refl _ _, Keep.refl _ _⟩

/-- The two tries, if `j < 256`. -/
theorem rbMid_ok {η : Nat} (hη : η = 2 ∨ η = 4) (s : State) {aP : Addr} {L : List Zq} (hbp : s.gpr .rbp = aP)
    (hdi : s.gpr .rdi = BitVec.ofNat 64 L.length) (hL : L.length ≤ 256) (hw : pR aP ∈ s.wr)
    (hst : Stored s.mem aP L) (hcf : s.cf = some (decide ((s.gpr .rdi).toNat < 256))) {z : Byte}
    (hax : s.gpr .rax = BitVec.setWidth 64 z) (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 (z.toNat % 16)) :
    WP isa (.ite .b (.seq (rbTry η) (.seq (.block rbHi) (.ite .b (rbTry η) (.block [])))) (.block [])) s
      fun s' => s'.gpr .rdi = BitVec.ofNat 64 (rbStep η L z).length ∧ Stored s'.mem aP (rbStep η L z) ∧
        Frame [pR aP] s.mem s'.mem ∧ Keep [.rax, .rdx, .r8, .rdi] s s' := by
  have hl : (s.gpr .rdi).toNat = L.length := by rw [hdi, ofNat64_toNat (by omega)]
  rw [rbStep_eq]
  refine WP.ite (decide (L.length < 256)) (by rw [← hl]; exact hcf) (fun hbb => ?_) (fun hbb => ?_)
  · simp only [decide_eq_true_eq] at hbb
    rw [ifT hbb]
    refine WP.seq (WP.mono (rbTry_ok hη s ⟨hbp, hdi, hbb, hw, hst⟩ (Nat.mod_lt _ (by decide)) hdx)
      fun s1 ⟨hdi1, hst1, hf1, k1⟩ => ?_)
    refine WP.seq (WP.mono (rbHi_ok s1 (z := z) (by rw [k1.gpr (by decide), hax]))
      fun s2 ⟨⟨hdx2, hcf2, hm2, hdi2⟩, k2⟩ => ?_)
    refine WP.mono (rbMid2_ok hη s2 (aP := aP) (L := hbTry η L (z.toNat % 16)) (by rw [k2.gpr (by decide), k1.gpr (by decide), hbp])
      (by rw [hdi2, hdi1]) (hbTry_length_le hbb _) (by rw [k2.2.2, k1.2.2]; exact hw) (by rw [hm2]; exact hst1)
      (by rw [hcf2, hdi2]) (by have := z.isLt; omega) hdx2) fun s3 ⟨hdi3, hst3, hf3, k3⟩ => ?_
    exact ⟨hdi3, hst3, hf1.trans (by rw [← hm2]; exact hf3), ((k1.trans k2).trans k3).mono (by simp)⟩
  · simp only [decide_eq_false_iff_not] at hbb
    rw [ifF hbb]
    exact WP.block_nil ⟨hdi, hst, Frame.refl _ _, Keep.refl _ _⟩

theorem sx1' : BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 := by decide

/-- An iteration: what `rbStep` does to the coefficients `L`. -/
theorem rbBody_ok {η : Nat} (hη : η = 2 ∨ η = 4) (s : State) {aP : Addr} {L : List Zq} (hbp : s.gpr .rbp = aP)
    (hdi : s.gpr .rdi = BitVec.ofNat 64 L.length) (hL : L.length ≤ 256) (hw : pR aP ∈ s.wr)
    (hst : Stored s.mem aP L) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1) :
    WP isa (rbBody η) s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (rbStep η L (s.mem (s.gpr .rsi))).length ∧
      Stored s'.mem aP (rbStep η L (s.mem (s.gpr .rsi))) ∧
      Frame [pR aP] s.mem s'.mem ∧ s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 1 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ Keep [.rax, .rdx, .r8, .rdi, .rsi, .rcx] s s' := by
  refine WP.seq (WP.mono (rbLoad_ok s h0) fun s1 ⟨⟨hax, hdx, hcf, hm1, hdi1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (rbMid_ok hη s1 (aP := aP) (L := L) (by rw [k1.gpr (by decide), hbp]) (by rw [hdi1, hdi])
    hL (by rw [k1.2.2]; exact hw) (by rw [hm1]; exact hst) (by rw [hcf, hdi1]) hax hdx)
    fun s3 ⟨hdi3, hst3, hf3, k3⟩ => ?_)
  refine WP.mono (step_ok s3 1) fun s4 ⟨⟨hsi4, hcx4, hz4, hm4⟩, k4⟩ => ?_
  have hsi3 : s3.gpr .rsi = s.gpr .rsi := by rw [k3.gpr (by decide), k1.gpr (by decide)]
  have hcx3 : s3.gpr .rcx = s.gpr .rcx := by rw [k3.gpr (by decide), k1.gpr (by decide)]
  exact ⟨by rw [k4.gpr (by decide), hdi3], by rw [hm4]; exact hst3, by rw [hm4, ← hm1]; exact hf3,
    by rw [hsi4, hsi3, sx1'], by rw [hcx4, hcx3], by rw [hz4, hcx3], ((k1.trans k3).trans k4).mono (by simp)⟩

end VG.Proof.MlDsa.X86_64.Sample
