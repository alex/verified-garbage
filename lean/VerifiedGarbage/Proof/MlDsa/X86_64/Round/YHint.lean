import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YNorm
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.MakeHint

/-!
# ML-DSA on x86-64: `vg_mldsa_make_hint_avx2`

In each doubleword, `mhX` computes the hint bit (`mhL`, `mhL_toNat`); the loop
stores the eight hints of an iteration and adds their count, the sum of the
nibbles of the byte mask of the hints shifted to bit 7 (`cntH_ok`, `nib_sp`),
to `r9`.
-/

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa
open VG.Proof.MlKem.X86_64 (Keep XOnly YOnly ylanes ifp ifn WP.keep)
open VG.Impl.MlKem.X86_64 (xb xmov toY)
open VG.Proof.MlDsa.X86_64.Arith (qV csubL csubL_toNat dword_csubV bc)

/-! ## A doubleword -/

/-- The hint bit `mhX` computes from `z` and `r`. -/
def mhL (g : Nat) (z r : BitVec 32) : BitVec 32 :=
  ((hbL g (csubL (r + z)) ^^^ hbL g r) + BitVec.ofNat 32 63) >>> 6

theorem mhL_toNat {g : Nat} (h : g ∈ gamma2s) {z r : BitVec 32} (hz : z.toNat < q) (hr : r.toNat < q) :
    (mhL g z r).toNat = (makeHint g (Fin.ofNat q z.toNat) (Fin.ofNat q r.toNat)).toNat := by
  have e1 : (r + z).toNat = r.toNat + z.toNat := by
    rw [BitVec.toNat_add]; rw [q_eq] at hz hr; omega
  have e2 : (csubL (r + z)).toNat = (r.toNat + z.toNat) % q := by
    rw [csubL_toNat (by rw [e1]; omega), e1, VG.Proof.MlDsa.Arith.condSub]
    split <;> rw [q_eq] at * <;> omega
  have hs : (csubL (r + z)).toNat < q := by rw [e2]; exact Nat.mod_lt _ (by decide)
  have hM : hbM g ≤ 44 ∧ 0 < hbM g := by rcases mem_gamma2s h with rfl | rfl <;> decide
  have hu := Nat.mod_lt (hbF g ((r.toNat + z.toNat) % q)) hM.2
  have hv := Nat.mod_lt (hbF g r.toNat) hM.2
  have hx : hbF g ((r.toNat + z.toNat) % q) % hbM g ^^^ hbF g r.toNat % hbM g < 2 ^ 6 :=
    Nat.xor_lt_two_pow (by omega) (by omega)
  have hvz : (Fin.ofNat q z.toNat).val = z.toNat := Nat.mod_eq_of_lt hz
  have hvr : (Fin.ofNat q r.toNat).val = r.toNat := Nat.mod_eq_of_lt hr
  rw [makeHint_eq h, hvz, hvr, mhL, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_xor,
    hbL_toNat h hs, hbL_toNat h hr, e2, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  by_cases e : hbF g r.toNat % hbM g = hbF g ((r.toNat + z.toNat) % q) % hbM g
  · rw [decide_eq_false (fun h' => h' e), e, Nat.xor_self]; rfl
  · rw [decide_eq_true e]
    have : hbF g ((r.toNat + z.toNat) % q) % hbM g ^^^ hbF g r.toNat % hbM g ≠ 0 :=
      fun h' => e (xor_eq_zero h').symm
    show _ = 1
    omega

theorem mhL_le {g : Nat} (h : g ∈ gamma2s) {z r : BitVec 32} (hz : z.toNat < q) (hr : r.toNat < q) :
    (mhL g z r).toNat ≤ 1 := by
  rw [mhL_toNat h hz hr]; exact Bool.toNat_le _

/-! ## The code on a register -/

theorem mhMid_ok (s : State) (hq : s.xmm .xmm15 = qV) :
    WP isa (.block mhMid) s fun s' => s'.xmm .xmm3 = s.xmm .xmm0 ∧
      (∀ e < 4, dword (s'.xmm .xmm0) e = csubL (dword (s.xmm .xmm4) e + dword (s.xmm .xmm5) e)) ∧
      XOnly [.xmm0, .xmm1, .xmm3] s s' := by
  simp only [mhMid, VG.Impl.MlDsa.X86_64.Arith.vcsub, VG.Impl.MlDsa.X86_64.Arith.vcadd, xmov, xb, List.cons_append,
    List.nil_append]
  vrun [VG.X86_64.eval_movdqa]
  refine ⟨trivial, fun e he => ?_, by xonly⟩
  rw [hq, ← dword_paddd _ _ he, ← dword_csubV _ he]
  rfl

theorem mhTail_ok (s : State) (h11 : Bc (s.xmm .xmm11) (BitVec.ofNat 32 63)) :
    WP isa (.block mhTail) s fun s' => (∀ e < 4,
      dword (s'.xmm .xmm0) e = ((dword (s.xmm .xmm0) e ^^^ dword (s.xmm .xmm3) e) + BitVec.ofNat 32 63) >>> 6 ∧
      dword (s'.xmm .xmm1) e = (((dword (s.xmm .xmm0) e ^^^ dword (s.xmm .xmm3) e) + BitVec.ofNat 32 63) >>> 6) <<< 7) ∧
      XOnly [.xmm0, .xmm1] s s' := by
  simp only [mhTail, xmov, xb]
  vrun [VG.X86_64.eval_movdqa]
  refine ⟨fun e he => ?_, by xonly⟩
  simp (disch := first | decide | assumption) only [dword_pxor, dword_paddd, dword_psrld, dword_pslld, h11 e he]
  exact ⟨rfl, rfl⟩

theorem mhX_ok {g : Nat} (hg : g = g32 ∨ g = g88) (s : State) (hc : HbC g s) (hq : s.xmm .xmm15 = qV)
    (h11 : Bc (s.xmm .xmm11) (BitVec.ofNat 32 63)) :
    WP isa (.block (mhX g)) s fun s' => (∀ e < 4,
      dword (s'.xmm .xmm0) e = mhL g (dword (s.xmm .xmm5) e) (dword (s.xmm .xmm0) e) ∧
      dword (s'.xmm .xmm1) e = mhL g (dword (s.xmm .xmm5) e) (dword (s.xmm .xmm0) e) <<< 7) ∧
      XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] s s' := by
  rw [mhX, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (Q := fun (s1 : State) => s1.xmm .xmm4 = s.xmm .xmm0 ∧ XOnly [.xmm4] s s1)
    (by simp only [xmov, xb]; vrun [VG.X86_64.eval_movdqa]; exact ⟨trivial, by xonly⟩) fun s1 ⟨a1, o1⟩ => ?_
  have hc1 : HbC g s1 := ⟨by rw [o1.xmm _ (by decide)]; exact hc.c8, by rw [o1.xmm _ (by decide)]; exact hc.c9,
    by rw [o1.xmm _ (by decide)]; exact hc.c10⟩
  rw [WP.block_append_iff]
  refine WP.mono (hbX_ok hg s1 hc1) fun s2 ⟨a2, o2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mhMid_ok s2 (by rw [o2.xmm _ (by decide), o1.xmm _ (by decide), hq])) fun s3 ⟨b3, a3, o3⟩ => ?_
  have hc3 : HbC g s3 := ⟨by rw [o3.xmm _ (by decide), o2.xmm _ (by decide)]; exact hc1.c8,
    by rw [o3.xmm _ (by decide), o2.xmm _ (by decide)]; exact hc1.c9,
    by rw [o3.xmm _ (by decide), o2.xmm _ (by decide)]; exact hc1.c10⟩
  rw [WP.block_append_iff]
  refine WP.mono (hbX_ok hg s3 hc3) fun s4 ⟨a4, o4⟩ => ?_
  refine WP.mono (mhTail_ok s4 (by
    rw [o4.xmm _ (by decide), o3.xmm _ (by decide), o2.xmm _ (by decide), o1.xmm _ (by decide)]; exact h11))
    fun s5 ⟨a5, o5⟩ => ⟨fun e he => ?_, ?_⟩
  · have hz : dword (s4.xmm .xmm0) e = hbL g (csubL (dword (s.xmm .xmm0) e + dword (s.xmm .xmm5) e)) := by
      rw [a4 e he, a3 e he, o2.xmm _ (by decide), a1, o2.xmm _ (by decide), o1.xmm _ (by decide)]
    have hr1 : dword (s4.xmm .xmm3) e = hbL g (dword (s.xmm .xmm0) e) := by
      rw [o4.xmm _ (by decide), b3, a2 e he, o1.xmm _ (by decide)]
    rw [(a5 e he).1, (a5 e he).2, hz, hr1]
    exact ⟨rfl, rfl⟩
  · exact ((((o1.trans o2).trans o3).trans o4).trans o5).mono (by simp)

/-! ## The count -/

/-- What `cntH` leaves in `eax`: the sum of the nibbles of `x`, if it fits in one. -/
def nib (x : BitVec 32) : BitVec 32 :=
  let x1 := x + x >>> 4
  let x2 := x1 + x1 >>> 8
  (x2 + x2 >>> 16) &&& 15

/-- The eight bits `b d` at bits `4d`. -/
def sp (b : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => sp b k + (b k).toNat * 16 ^ k

/-- The number of the first `k` bits set. -/
def cnt8 (b : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => cnt8 b k + (b k).toNat

theorem nib_bools : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (nib (BitVec.ofNat 32 (b0.toNat + b1.toNat * 16 + b2.toNat * 16 ^ 2 + b3.toNat * 16 ^ 3 + b4.toNat * 16 ^ 4 +
      b5.toNat * 16 ^ 5 + b6.toNat * 16 ^ 6 + b7.toNat * 16 ^ 7))).toNat =
      b0.toNat + b1.toNat + b2.toNat + b3.toNat + b4.toNat + b5.toNat + b6.toNat + b7.toNat := by
  decide +kernel

theorem nib_sp (b : Nat → Bool) : (nib (BitVec.ofNat 32 (sp b 8))).toNat = cnt8 b 8 := by
  have := nib_bools (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7)
  simp only [sp, cnt8, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.pow_one] at this ⊢
  exact this

/-- A byte mask with bit `4d` the bit `b d`, and the others clear. -/
theorem bsum_sp {f : Nat → Bool} {b : Nat → Bool} : ∀ k, (∀ j < 4 * k, f j = (decide (j % 4 = 0) && b (j / 4))) →
    VG.Proof.MlKem.X86_64.S4.bsum f (4 * k) = sp b k
  | 0, _ => rfl
  | k + 1, h => by
    have ih := bsum_sp k fun j hj => h j (by omega)
    rw [show 4 * (k + 1) = 4 * k + 1 + 1 + 1 + 1 by omega]
    simp only [VG.Proof.MlKem.X86_64.S4.bsum, sp]
    rw [ih, h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]
    simp only [show (4 * k) % 4 = 0 by omega, show (4 * k + 1) % 4 = 1 by omega, show (4 * k + 2) % 4 = 2 by omega,
      show (4 * k + 1 + 1 + 1) % 4 = 3 by omega, show 4 * k / 4 = k by omega,
      decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.toNat_false, Nat.zero_mul, Nat.add_zero,
      show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 0 by decide]
    rw [show 2 ^ (4 * k) = 16 ^ k by rw [Nat.pow_mul]]

theorem cntH_ok (s : State) :
    WP isa (.block cntH) s fun s' =>
      (s'.gpr .r9 = s.gpr .r9 + BitVec.setWidth 64 (nib ((s.gpr .rax).setWidth 32)) ∧ s'.mem = s.mem ∧
        ∀ r l, s'.lane r l = s.lane r l) ∧ Keep [.rax, .rdx, .r9] s s' := by
  refine WP.keep _ ?_ (by decide)
  simp only [cntH]
  xrun
  exact ⟨rfl, fun _ _ => rfl⟩

end VG.Proof.MlDsa.X86_64.Round

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.X86_64.Round (HbC Bc bc_ofDwords mhL mhL_le mhX_ok nib sp cnt8 nib_sp bsum_sp ymm_bit cntH_ok
  sw3264)
open VG.Proof.MlKem.X86_64 (Keep XOnly YOnly ylanes yld_ok yconst_ok wp_rcxLoopY ifp ifn ptr_step add_ofNat_zero
  lane_setReg lane_setFlags sx32 State.setMem_ymm)
open VG.Impl.MlKem.X86_64 (toY)
open VG.Spec.MlDsa (q n coeffAt Reduced gamma2s)

/-- `Σ k < m, f k`. -/
def csum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => csum f m + f m

namespace YHintL

/-- After `i` vectors of eight. -/
structure Inv (s₀ : State) (g : Nat) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = s₀.gpr .rdi + BitVec.ofNat 64 (32 * i)
  rsi : s.gpr .rsi = s₀.gpr .rsi + BitVec.ofNat 64 (32 * i)
  r10 : s.gpr .r10 = s₀.gpr .rcx + BitVec.ofNat 64 (32 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  yc : YC g s
  c11 : ∀ l < 2, s.lane .xmm11 l = bc (BitVec.ofNat 32 63)
  frame : Frame [pR (s₀.gpr .rcx)] s₀.mem s.mem
  coeff : ∀ k < 256, coeffAt s.mem (s₀.gpr .rcx) k = if k < 8 * i then
    mhL g (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k) else coeffAt s₀.mem (s₀.gpr .rcx) k
  r9 : (s.gpr .r9).toNat =
    csum (fun k => (mhL g (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)).toNat) (8 * i)

theorem lane_mhX (g : Nat) (hg : g = g32 ∨ g = g88) : laneSseBlock (toY (mhX g)) = some (mhX g) := by
  rcases hg with rfl | rfl <;> decide +kernel

/-- The constants are kept by code that writes only `xmm0` to `xmm5`. -/
theorem keep_consts {g : Nat} {s s' : State} (hyc : YC g s) (h11 : ∀ l < 2, s.lane .xmm11 l = bc (BitVec.ofNat 32 63))
    {rs : List XReg} (hr : ∀ r ∈ rs, r ∈ [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5])
    (hl : ∀ r ∉ rs, ∀ l < 2, s'.lane r l = s.lane r l) :
    YC g s' ∧ ∀ l < 2, s'.lane .xmm11 l = bc (BitVec.ofNat 32 63) := by
  have n : ∀ r ∈ [XReg.xmm8, .xmm9, .xmm10, .xmm11, .xmm15], r ∉ rs := fun r hr' hr'' => by
    have := hr r hr''; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' this
    rcases hr' with rfl | rfl | rfl | rfl | rfl <;> rcases this with h | h | h | h | h | h <;> cases h
  refine ⟨fun l hl' => ?_, fun l hl' => by rw [hl _ (n _ (by simp)) l hl']; exact h11 l hl'⟩
  rw [hl _ (n _ (by simp)) l hl', hl _ (n _ (by simp)) l hl', hl _ (n _ (by simp)) l hl', hl _ (n _ (by simp)) l hl']
  exact hyc l hl'

/-- A hint shifted to bit 7: bit `8m + 7` is the hint's bit 0 if `m = 0`, and clear otherwise. -/
theorem shl7_bit {v : BitVec 32} (hv : v.toNat ≤ 1) {m : Nat} (hm : m < 4) :
    (v <<< 7).getLsbD (8 * m + 7) = (decide (m = 0) && v.getLsbD 0) := by
  rw [BitVec.getLsbD_shiftLeft]
  rcases (by omega : m = 0 ∨ 0 < m) with rfl | h
  · simp
  · have : v.getLsbD (8 * m) = false := by
      rw [← BitVec.testBit_toNat, Nat.testBit_lt_two_pow (Nat.lt_of_le_of_lt hv
        (Nat.one_lt_two_pow (by omega)))]
    simp [show 8 * m + 7 - 7 = 8 * m by omega, this, show m ≠ 0 by omega]

theorem bit0_toNat {v : BitVec 32} (hv : v.toNat ≤ 1) : (v.getLsbD 0).toNat = v.toNat := by
  rw [← BitVec.testBit_toNat, Nat.testBit_zero]
  rcases (by omega : v.toNat = 0 ∨ v.toNat = 1) with h | h <;> rw [h] <;> rfl

theorem csum_le {f : Nat → Nat} : ∀ {m : Nat}, (∀ k < m, f k ≤ 1) → csum f m ≤ m
  | 0, _ => Nat.le_refl _
  | m + 1, h => by
    have := csum_le (m := m) fun k hk => h k (by omega)
    have := h m (by omega)
    simp only [csum]; omega

theorem csum8 (f : Nat → Nat) (b : Nat → Bool) (m : Nat) (h : ∀ d < 8, (b d).toNat = f (m + d)) :
    csum f (m + 8) = csum f m + cnt8 b 8 := by
  rw [show csum f (m + 8) = csum f m + f m + f (m + 1) + f (m + 2) + f (m + 3) + f (m + 4) + f (m + 5) +
      f (m + 6) + f (m + 7) from rfl,
    show cnt8 b 8 = (b 0).toNat + (b 1).toNat + (b 2).toNat + (b 3).toNat + (b 4).toNat + (b 5).toNat +
      (b 6).toNat + (b 7).toNat by simp [cnt8],
    h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide),
    h 6 (by decide), h 7 (by decide)]
  simp only [Nat.add_zero]
  omega

section
variable {s₀ : State} (hrd : s₀.rd = [pR (s₀.gpr .rdi), pR (s₀.gpr .rsi)]) (hwr : s₀.wr = [pR (s₀.gpr .rcx)])
  (hdz : (pR (s₀.gpr .rdi)).Disjoint (pR (s₀.gpr .rcx))) (hdr : (pR (s₀.gpr .rsi)).Disjoint (pR (s₀.gpr .rcx)))
  (hz : Reduced s₀.mem (s₀.gpr .rdi)) (hr : Reduced s₀.mem (s₀.gpr .rsi)) {g : Nat} (hg : g = g32 ∨ g = g88)
include hrd hwr hdz hdr hz hr hg

theorem step {i : Nat} (hi : i < 32) {s : State} (hI : Inv s₀ g i s) :
    WP isa (.block (mhBodyY g ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      Inv s₀ g (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hg' : g ∈ gamma2s := by rcases hg with rfl | rfl <;> decide
  have j0 : 8 * i + 8 ≤ 256 := by omega
  have hw : pR (s₀.gpr .rcx) ∈ s.wr := by rw [hI.wr, hwr]; simp
  have hrz : pR (s₀.gpr .rdi) ∈ s.rd ++ s.wr := by rw [hI.rd, hrd]; simp
  have hrr : pR (s₀.gpr .rsi) ∈ s.rd ++ s.wr := by rw [hI.rd, hrd]; simp
  have e1 : s.gpr .rsi + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .rsi) (8 * i) := by
    rw [add_ofNat_zero, hI.rsi]; congr 2; omega
  have e2 : s.gpr .rdi + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .rdi) (8 * i) := by
    rw [add_ofNat_zero, hI.rdi]; congr 2; omega
  have e3 : s.gpr .r10 = coeffAddr (s₀.gpr .rcx) (8 * i) := by rw [hI.r10]; congr 2; omega
  rw [mhBodyY, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    show ∀ a b : Instr, [a, b] = [a] ++ [b] from fun _ _ => rfl, List.append_assoc, WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [e1]; exact f_in32 hrr j0)) fun s1 ⟨L1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr, e2]; exact f_in32 hrz j0)) fun s2 ⟨L2, o2⟩ => ?_
  have k2 := keep_consts hI.yc hI.c11 (rs := [.xmm0, .xmm5]) (by simp) fun r hr' l hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [o2.lane r (by simp [hr'.2]) l hl, o1.lane r (by simp [hr'.1]) l hl]
  rw [WP.block_append_iff]
  refine WP.mono (ylanes (lane_mhX g hg) (P := fun l t => ∀ e < 4,
      dword (t.xmm .xmm0) e = mhL g (dword ((s2.proj l).xmm .xmm5) e) (dword ((s2.proj l).xmm .xmm0) e) ∧
      dword (t.xmm .xmm1) e = mhL g (dword ((s2.proj l).xmm .xmm5) e) (dword ((s2.proj l).xmm .xmm0) e) <<< 7)
    fun l hl => mhX_ok hg _ (k2.1.hbc hl) (k2.1.q hl)
      (by rw [State.proj_xmm, k2.2 l hl]; exact bc_ofDwords _)) fun s3 ⟨B3, o3⟩ => ?_
  have o13 := (o1.trans o2).trans o3
  have k3 := keep_consts k2.1 k2.2 (rs := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4]) (by simp) o3.lane
  have g3 : s3.gpr .r10 = coeffAddr (s₀.gpr .rcx) (8 * i) := by rw [o13.gpr, e3]
  have w0 : InRegions s3.wr (s3.gpr .r10) 32 := by rw [o13.wr, g3]; exact f_in32 hw j0
  -- The values of the lanes.
  have hv : ∀ l < 2, ∀ e < 4, mhL g (dword ((s2.proj l).xmm .xmm5) e) (dword ((s2.proj l).xmm .xmm0) e) =
      mhL g (coeffAt s₀.mem (s₀.gpr .rdi) (8 * i + 4 * l + e)) (coeffAt s₀.mem (s₀.gpr .rsi) (8 * i + 4 * l + e)) :=
    fun l hl e he => by
      rw [State.proj_xmm, State.proj_xmm, L2 l hl, o2.lane _ (by decide) l hl, L1 l hl, o1.mem, o1.gpr, e1, e2,
        dword_readW _ _ he, dword_readW _ _ he, lane_load, lane_load, coeffAddr_add, coeffAddr_add, ← coeffAt_eq,
        ← coeffAt_eq, coeffAt_frame hI.frame (by simpa using hdz) (by rw [n_eq]; omega),
        coeffAt_frame hI.frame (by simpa using hdr) (by rw [n_eq]; omega)]
  have hle : ∀ k < 256, (mhL g (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)).toNat ≤ 1 :=
    fun k hk => mhL_le hg' (hz k (by rw [n_eq]; exact hk)) (hr k (by rw [n_eq]; exact hk))
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s4 : State) => s4.mem = s3.mem.writeW (s3.gpr .r10) (s3.ymm .xmm0) ∧
      s4.gpr = (s3.setReg .rax (byteMask (s3.ymm .xmm1) 32)).gpr ∧ s4.rd = s3.rd ∧ s4.wr = s3.wr ∧
      ∀ r l, s4.lane r l = s3.lane r l)
    (by
      vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd,
        State.setMem_ymm, w0]
      exact ⟨rfl, fun r l => by simp only [lane_setReg, State.setMem_lane]⟩) fun s4 ⟨m4, g4, r4, w4, l4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cntH_ok s4) fun s5 ⟨⟨h9, m5, l5⟩, k5⟩ => ?_
  have hax : s4.gpr .rax = byteMask (s3.ymm .xmm1) 32 := by rw [g4, RegUpd.gpr_setReg_self]
  -- The count of the eight hints.
  let b : Nat → Bool := fun d =>
    (mhL g (coeffAt s₀.mem (s₀.gpr .rdi) (8 * i + d)) (coeffAt s₀.mem (s₀.gpr .rsi) (8 * i + d))).getLsbD 0
  have hbits : ∀ j < 4 * 8, (s3.ymm .xmm1).getLsbD (8 * j + 7) = (decide (j % 4 = 0) && b (j / 4)) := fun j hj => by
    have hl : j / 16 < 2 := by omega
    have he : j % 16 / 4 < 4 := by omega
    rw [ymm_bit _ _ (by omega), ← State.proj_xmm, (B3 _ hl _ he).2, hv _ hl _ he,
      shl7_bit (hle _ (by omega)) (by omega)]
    simp only [b, show 8 * i + 4 * (j / 16) + j % 16 / 4 = 8 * i + j / 4 by omega]
  have hcnt : (BitVec.setWidth 64 (nib ((s4.gpr .rax).setWidth 32))).toNat = cnt8 b 8 := by
    rw [hax, VG.Proof.MlKem.X86_64.S4.byteMask_eq _ (by decide), BitVec.toNat_setWidth,
      show BitVec.setWidth 32 (BitVec.ofNat 64 (VG.Proof.MlKem.X86_64.S4.bsum
        (fun i => (s3.ymm .xmm1).getLsbD (8 * i + 7)) 32)) =
        BitVec.ofNat 32 (VG.Proof.MlKem.X86_64.S4.bsum (fun i => (s3.ymm .xmm1).getLsbD (8 * i + 7)) 32) by
      apply BitVec.eq_of_toNat_eq
      have := VG.Proof.MlKem.X86_64.S4.bsum_lt (fun i => (s3.ymm .xmm1).getLsbD (8 * i + 7)) 32
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega,
      (bsum_sp 8 hbits : VG.Proof.MlKem.X86_64.S4.bsum _ 32 = _), nib_sp]
    have : cnt8 b 8 ≤ 8 := by
      simp only [cnt8]
      have hb := fun d => Bool.toNat_le (b d)
      have := hb 0; have := hb 1; have := hb 2; have := hb 3; have := hb 4; have := hb 5
      have := hb 6; have := hb 7
      omega
    have := (nib_sp b).symm ▸ this
    omega
  simp only [List.cons_append, List.nil_append]
  xrun
  have G5 : ∀ r, r ∉ [Reg.rax, .rdx, .r9] → s5.gpr r = s.gpr r := fun r hr => by
    rw [k5.gpr hr, g4, RegUpd.gpr_setReg_of_ne _ _ (fun h => hr (by simp [h])), o13.gpr]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_⟩, by rw [G5 .rcx (by simp)], by rw [G5 .rcx (by simp)]⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [G5 .rdi (by simp), hI.rdi]; exact ptr_step _ i 32
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [G5 .rsi (by simp), hI.rsi]; exact ptr_step _ i 32
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [G5 .r10 (by simp), hI.r10]; exact ptr_step _ i 32
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; rw [k5.2.1, r4, o13.rd, hI.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; rw [k5.2.2, w4, o13.wr, hI.wr]
  · exact k3.1.keep (rs := []) (by simp) fun r _ l _ => by simp only [lane_setReg, lane_setFlags]; rw [l5, l4]
  · intro l hl; simp only [lane_setReg, lane_setFlags]; rw [l5, l4]; exact k3.2 l hl
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    rw [m5, m4, g3, o13.mem]; exact hI.frame.writeW (List.mem_singleton_self _) _ (pR_contains32 _ j0)
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    rw [m5, m4, g3, o13.mem, coeffAt_write256 _ _ j0 _ hk]
    split
    · rename_i h
      rw [ifp (show k < 8 * (i + 1) by omega), State.ymm, extract_ymm _ _ (by omega)]
      have hc : ∀ l < 2, ∀ e < 4, dword (s3.lane .xmm0 l) e =
          mhL g (coeffAt s₀.mem (s₀.gpr .rdi) (8 * i + 4 * l + e)) (coeffAt s₀.mem (s₀.gpr .rsi) (8 * i + 4 * l + e)) :=
        fun l hl e he => by rw [← State.proj_xmm, (B3 l hl e he).1, hv l hl e he]
      split
      · rename_i h4
        have := hc 0 (by decide) (k - 8 * i) h4
        rw [show 8 * i + 4 * 0 + (k - 8 * i) = k by omega] at this
        exact this
      · rename_i h4
        have := hc 1 (by decide) (k - 8 * i - 4) (by omega)
        rw [show 8 * i + 4 * 1 + (k - 8 * i - 4) = k by omega] at this
        exact this
    · rename_i h
      rw [hI.coeff k hk]
      by_cases h' : k < 8 * i
      · rw [ifp h', ifp (by omega)]
      · rw [ifn h', ifn (by omega)]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]
    have h94 : s4.gpr .r9 = s.gpr .r9 := by
      rw [g4, RegUpd.gpr_setReg_of_ne _ _ (by decide), o13.gpr]
    have e8 := csum8 (fun k => (mhL g (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)).toNat) b
      (8 * i) fun d hd => bit0_toNat (hle _ (by omega))
    have hb := csum_le (f := fun k => (mhL g (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)).toNat)
      (m := 8 * i + 8) fun k hk => hle k (by omega)
    rw [h9, BitVec.toNat_add, hcnt, h94, hI.r9, show 8 * (i + 1) = 8 * i + 8 by omega, e8]
    rw [e8] at hb
    exact Nat.mod_eq_of_lt (by omega)

/-- The constants and the loop: the hints at `h`, and their count in `r9`. -/
theorem loop_ok {s : State} (hs0 : s.gpr .rdi = s₀.gpr .rdi) (hs1 : s.gpr .rsi = s₀.gpr .rsi)
    (hs10 : s.gpr .r10 = s₀.gpr .rcx) (hs9 : s.gpr .r9 = 0) (hsrd : s.rd = s₀.rd) (hswr : s.wr = s₀.wr)
    (hsm : s.mem = s₀.mem) :
    WP isa (mhY g) s fun s' => Frame [pR (s₀.gpr .rcx)] s₀.mem s'.mem ∧
      (∀ k < 256, coeffAt s'.mem (s₀.gpr .rcx) k =
        mhL g (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) ∧
      (s'.gpr .r9).toNat =
        csum (fun k => (mhL g (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)).toNat) 256 := by
  unfold mhY
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (yC_ok g s) fun w ⟨yc, k1, m1, _, _⟩ =>
    WP.mono (yconst_ok .xmm11 63 w) fun w2 ⟨l2, k2, m2, _, o2⟩ => ?_
  have yc2 : YC g w2 := fun l hl => by
    rw [o2 .xmm8 (by decide) l hl, o2 .xmm9 (by decide) l hl, o2 .xmm10 (by decide) l hl,
      o2 .xmm15 (by decide) l hl]
    exact yc l hl
  refine WP.mono (wp_rcxLoopY (N := 32) (by decide) (by decide) _ (fun u o hy _ =>
    ⟨by rw [o.keep.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide), Nat.mul_zero, add_ofNat_zero, hs0],
      by rw [o.keep.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide), Nat.mul_zero, add_ofNat_zero, hs1],
      by rw [o.keep.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide), Nat.mul_zero, add_ofNat_zero, hs10],
      by rw [o.keep.2.1, k2.2.1, k1.2.1, hsrd], by rw [o.keep.2.2, k2.2.2, k1.2.2, hswr],
      fun l hl => by simp only [State.lane]; rw [o.xmm, hy]; exact yc2 l hl,
      fun l hl => by simp only [State.lane]; rw [o.xmm, hy]; exact l2 l hl,
      by rw [o.mem, m2, m1, hsm]; exact Frame.refl _ _, fun k _ => by rw [o.mem, m2, m1, hsm, ifn (by omega)],
      by rw [o.keep.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide), hs9]; rfl⟩)
    fun i hi u hI => step hrd hwr hdz hdr hz hr hg hi hI) fun u hI => ⟨hI.frame, fun k hk => by
      rw [hI.coeff k hk, ifp (by omega)], hI.r9⟩

end

end YHintL

end VG.Proof.MlDsa.X86_64.Arith

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep gprPreserved_of)
open VG.Proof.MlDsa.X86_64.Arith (csum)

/-- The count of the hints is `onesFrom` them. -/
theorem csum_onesFrom (v : Vector Bool n) (f : Nat → Nat) (hf : ∀ k < 256, f k = v[k]!.toNat) :
    ∀ m ≤ 256, csum f m + onesFrom v m = onesFrom v 0
  | 0, _ => Nat.zero_add _
  | m + 1, hm => by
    have ih := csum_onesFrom v f hf m (by omega)
    rw [onesFrom_step v (by rw [n_eq]; omega), ← hf m (by omega)] at ih
    simp only [csum]; omega

section
variable {s₀ : State} (hp : makeHintK.pre s₀)
include hp

theorem makeHintY_correct : ∃ t s', Exec isa makeHintAvx2 s₀ t s' ∧ abiPreserved s₀ s' ∧ makeHintK.post s₀ s' := by
  have hg : arg32 s₀ .rdx ∈ gamma2s := hp.2.2.2.2.2.2.2.1
  have hz : Reduced s₀.mem (s₀.gpr .rdi) := hp.2.2.2.2.2.2.2.2.1
  have hr : Reduced s₀.mem (s₀.gpr .rsi) := hp.2.2.2.2.2.2.2.2.2
  let f : Nat → Nat := fun k =>
    (mhL (arg32 s₀ .rdx) (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)).toNat
  have wp : WP isa makeHintAvx2 s₀ fun s' => Frame [pR (s₀.gpr .rcx)] s₀.mem s'.mem ∧
      (∀ k < 256, coeffAt s'.mem (s₀.gpr .rcx) k =
        mhL (arg32 s₀ .rdx) (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) ∧
      (s'.gpr .rax).toNat = csum f 256 := by
    unfold makeHintAvx2
    refine WP.seq (WP.mono (mhPrologue_ok s₀) fun s₁ ⟨⟨h10, h9, hzf, hm⟩, hk⟩ => ?_)
    have go : ∀ g, arg32 s₀ .rdx = g → (g = g32 ∨ g = g88) → WP isa (mhY g) s₁ fun s' =>
        Frame [pR (s₀.gpr .rcx)] s₀.mem s'.mem ∧
        (∀ k < 256, coeffAt s'.mem (s₀.gpr .rcx) k =
          mhL (arg32 s₀ .rdx) (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) ∧
        (s'.gpr .r9).toNat = csum f 256 := fun g hge hg' => by
      subst hge
      exact Arith.YHintL.loop_ok hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hz hr hg' (hk.gpr (by decide))
        (hk.gpr (by decide)) h10 h9 hk.2.1 hk.2.2 hm
    have hite : WP isa (.ite .e (mhY g32) (mhY g88)) s₁ fun s' => Frame [pR (s₀.gpr .rcx)] s₀.mem s'.mem ∧
        (∀ k < 256, coeffAt s'.mem (s₀.gpr .rcx) k =
          mhL (arg32 s₀ .rdx) (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) ∧
        (s'.gpr .r9).toNat = csum f 256 := by
      refine WP.ite (M := isa) _ (show isa.eval .e s₁ = _ from hzf) (fun h => ?_) (fun h => ?_)
      · rw [sub_beq_zero32, decide_eq_true_eq] at h
        exact go _ ((gamma_cases hg).1 h) (.inl rfl)
      · rw [sub_beq_zero32, decide_eq_false_iff_not] at h
        exact go _ ((gamma_cases hg).2 h) (.inr rfl)
    refine WP.seq (WP.mono hite fun u ⟨hf, hc, h9'⟩ => ?_)
    refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.gpr .rax = u.gpr .r9) (by vrund; exact ⟨rfl, rfl⟩)
      fun u' ⟨hm', hax⟩ => ?_
    rw [hm', hax]
    exact ⟨hf, hc, h9'⟩
  obtain ⟨t, s', he, ⟨hf, hv, hax⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .rsi, .rdi, .r9, .r10] wp (by decide +kernel)
  refine ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf ?_), ?_, ?_⟩
  · simpa using hp.2.2.2.2.2.2.1
  · refine hintIs_of_toNat fun k hk' => ?_
    apply BitVec.eq_of_toNat_eq
    rw [hv k hk', mhL_toNat hg (hz k hk') (hr k hk'), zipWith_get _ _ _ hk', polyAt_get _ _ hk', polyAt_get _ _ hk']
    simp only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Bool.toNat_le _) (by decide))).symm
  · have e := csum_onesFrom (Vector.zipWith (makeHint (arg32 s₀ .rdx)) (polyAt s₀.mem (s₀.gpr .rdi))
      (polyAt s₀.mem (s₀.gpr .rsi))) f (fun k hk' => by
        rw [zipWith_get _ _ _ (by rw [n_eq]; exact hk'), polyAt_get _ _ (by rw [n_eq]; exact hk'),
          polyAt_get _ _ (by rw [n_eq]; exact hk')]
        exact mhL_toNat hg (hz k (by rw [n_eq]; exact hk')) (hr k (by rw [n_eq]; exact hk'))) 256 (Nat.le_refl _)
    have e0 : onesFrom (Vector.zipWith (makeHint (arg32 s₀ .rdx)) (polyAt s₀.mem (s₀.gpr .rdi))
        (polyAt s₀.mem (s₀.gpr .rsi))) 256 = 0 := onesFrom_n _
    have : (s'.gpr .rax).toNat ≤ 256 := by
      rw [hax]
      exact Arith.YHintL.csum_le fun k hk' => mhL_le hg (hz k (by rw [n_eq]; exact hk')) (hr k (by rw [n_eq]; exact hk'))
    rw [BitVec.toNat_setWidth, hintOnes_single]
    omega

end

theorem makeHintY_ct : ConstantTime isa makeHintK.pre makeHintK.pub makeHintAvx2 :=
  VG.Taint.constantTime (A := X86_64.taint) (regsLo [.rdi, .rsi, .rcx, .rsp] [.rdx])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1]) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.2.2.2.2)
    (by taint_decide)

theorem makeHintY_verified : Verified X86_64.target makeHintAvx2 (makeHintContract X86_64.abi) :=
  Verified.of_correct (fun _ hp => makeHintY_correct hp) makeHintY_ct (by
    round_implies [makeHintContract, makeHintSig, makeHintK, hintK, X86_64.abi, X86_64.argRegs] [hintSat]
      using hintSat)

end VG.Proof.MlDsa.X86_64.Round
