import VerifiedGarbage.Proof.Bignum.X86_64.PubOut

/-!
# `vg_rsa_public` on x86-64: the computation for a valid modulus

`main`, from the header that `entry` leaves, for a valid modulus: the
result `i2osp (x^e mod m)` (or zeros, if the input is not below `m`) to
`out`, the mask's low bit returned, and the saved registers restored
(`main_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

theorem main_eq : main = seqs ((loadSteps ++ restSteps) ++ ((r2Steps Mont.base) ++ (expSteps ++ outSteps))) := rfl

/-- What `main` starts from: the working space at `B` (its base in `rdi`),
the header `entry` leaves (`out`, `m`, its length `k`, `e`, its length `L`,
the input), and the byte strings outside the working space. -/
structure MainPre (s : State) (B : Addr) (Z k : Nat) (op np ep ip : Addr) (L : Nat)
    (nb eb xb : List Byte) : Prop where
  scr : Scr s B Z
  rdi : s.gpr .rdi = B
  z : slot ((k + 7) / 8) 8 ≤ Z
  k1 : 64 ≤ k
  k2 : k ≤ 1024
  hO : word s.mem B (8 * sOut) = op
  hN : word s.mem B (8 * sN) = np
  hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k
  hE : word s.mem B (8 * sE) = ep
  hL : word s.mem B (8 * sElen) = BitVec.ofNat 64 L
  hIn : word s.mem B (8 * sIn) = ip
  n : Src s B Z np nb
  x : Src s B Z ip xb
  e : Src s B Z ep eb
  nl : nb.length = k
  xl : xb.length = k
  el : eb.length = L
  L1 : 1 ≤ L
  L2 : L ≤ k
  out : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1
  outSep : ∀ j < k, Z ≤ ofs B (op + BitVec.ofNat 64 j)

/-- What `main` (and `fail`) leave: the result `r` (a number below `256^k`)
to `out`, the flag `c` returned, the saved registers restored, and memory
outside the working space and `out` unchanged. -/
structure MainPost (s t : State) (B : Addr) (Z k : Nat) (op : Addr) (r : Nat) (c : Bool) : Prop where
  bytes : (List.range k).map (fun i => t.mem (op + BitVec.ofNat 64 i)) = Spec.Rsa.i2osp r k
  rax : t.gpr .rax = BitVec.ofNat 64 c.toNat
  saved : ∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)
  frame : ∀ x, Z ≤ ofs B x → (∀ j < k, x ≠ op + BitVec.ofNat 64 j) → t.mem x = s.mem x
  keep : Keep mmRegs s t

theorem setupRanges_le (w : Nat) : ∀ r ∈ setupRanges w, r.1 + r.2 ≤ slot w 8 := by
  have := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have := slot_le (w := w) (show 0 < 8 by decide)
  have := slot_le (w := w) (show aN < 8 by decide)
  have := slot_le (w := w) (show aX < 8 by decide)
  have := slot_le (w := w) (show aOne < 8 by decide)
  simp only [setupRanges, loadRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [sW, sArr, sMinv, sMask, sFn] at * <;> omega

theorem setupRanges_fixed (w : Nat) :
    ∀ r ∈ setupRanges w, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16) := by
  have := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have := slot_le (w := w) (show 0 < 8 by decide)
  have h1 : slot w 0 ≤ slot w aN := by unfold slot; omega
  have h2 : slot w 0 ≤ slot w aX := by unfold slot; omega
  have h3 : slot w 0 ≤ slot w aOne := by unfold slot; omega
  simp only [setupRanges, loadRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [sW, sArr, sMinv, sMask, sFn] at * <;> omega

theorem r2Ranges_fixed (w : Nat) : ∀ r ∈ r2Ranges w, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16) := by
  have := hdr_lt_slot w aAcc (show 31 < 32 by decide)
  have := hdr_lt_slot w aTmp (show 31 < 32 by decide)
  have := hdr_lt_slot w aR2 (show 31 < 32 by decide)
  simp only [r2Ranges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sCnt, sFn] at * <;> omega

theorem expPhaseRanges_fixed (w : Nat) :
    ∀ r ∈ expPhaseRanges w, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16) := by
  have := hdr_lt_slot w aXm (show 31 < 32 by decide)
  have := hdr_lt_slot w aAcc (show 31 < 32 by decide)
  have := hdr_lt_slot w aTmp (show 31 < 32 by decide)
  have := hdr_lt_slot w aY (show 31 < 32 by decide)
  simp only [expPhaseRanges, expRanges, bitRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [sI, sV, sBit, sFn] at * <;> omega

/-- What a valid modulus gives: odd, above 1, its top word not zero. -/
theorem valid_facts {N k : Nat} (hv : Spec.Rsa.modulusValid N k = true) (hk : 64 ≤ k) :
    N % 2 = 1 ∧ 1 < N ∧ 2 ^ (64 * ((k + 7) / 8 - 1)) ≤ N := by
  rw [Spec.Rsa.modulusValid, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hv
  obtain ⟨⟨⟨h1, -⟩, -⟩, h4⟩ := hv
  have h4 := of_decide_eq_true h4
  have hp : 2 ^ (64 * ((k + 7) / 8 - 1)) ≤ 256 ^ (k - 1) := by
    rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have h256 : 256 ≤ 256 ^ (k - 1) := by
    have := Nat.pow_le_pow_right (n := 256) (by decide) (show 1 ≤ k - 1 by omega); simpa using this
  exact ⟨beq_iff_eq.mp h1, by omega, hp.trans h4⟩

/-- `main`, for a valid modulus `m`: `i2osp (x^e mod m)` if `x < m` and
zeros otherwise, and `x < m` returned. -/
theorem main_ok {s : State} {B : Addr} {Z k : Nat} {op np ep ip : Addr} {L : Nat} {nb eb xb : List Byte}
    (h : MainPre s B Z k op np ep ip L nb eb xb) (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    WP isa main s fun t => MainPost s t B Z k op
      (if Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb then
        Spec.Rsa.os2ip xb ^ Spec.Rsa.os2ip eb % Spec.Rsa.os2ip nb else 0)
      (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) := by
  obtain ⟨hodd, hN1, hlo⟩ := valid_facts hv h.k1
  have hk1 := h.k1
  have hk2 := h.k2
  have hL2 := h.L2
  have hZ := h.z
  have hn := h.scr.nowrap
  have hn' : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega
  have hZs : ∀ {rs : List (Nat × Nat)}, (∀ r ∈ rs, r.1 + r.2 ≤ slot ((k + 7) / 8) 8) → ∀ r ∈ rs, r.1 + r.2 ≤ Z :=
    fun h' r hr => (h' r hr).trans hZ
  rw [main_eq]
  refine wp_seqs_append (by simp [loadSteps]) (by simp [r2Steps])
    (WP.mono (setup_ok h.scr h.rdi hZ (by omega) (by omega) h.hK h.hN h.hIn h.n h.x h.nl h.xl hodd)
      fun t₁ ⟨minv, so, f₁, k₁⟩ => ?_)
  have x₁ := Fixed.of_frm f₁ (setupRanges_fixed _)
  have i₁ := InScr.of_frm f₁ (hZs (setupRanges_le _))
  refine wp_seqs_append (by simp [r2Steps]) (by simp [expSteps])
    (WP.mono (r2_ok Mont.base so.good hZ (by omega) (by omega) so.n so.inv so.r12 so.r10 hodd hlo)
      fun t₂ ⟨hg₂, hlt₂, hr₂, f₂, k₂⟩ => ?_)
  have x₂ := Fixed.of_frm f₂ (r2Ranges_fixed _)
  have i₂ := InScr.of_frm f₂ (hZs (r2Ranges_le _))
  have x₁₂ := x₁.trans x₂
  refine wp_seqs_append (by simp [expSteps]) (by simp [outSteps])
    (WP.mono (expPhase_ok (X := Spec.Rsa.os2ip xb) hg₂ hZ (by omega) (by omega) hodd hN1
      (by rw [f₂.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact so.n)
      (by rw [f₂.r2_word hn' (by decide) (by decide) (by decide) (by decide)]; exact so.inv)
      (by rw [f₂.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact so.x)
      (by rw [f₂.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact so.one)
      hlt₂ hr₂ (by rw [x₁₂ sE (by decide)]; exact h.hE) (by rw [x₁₂ sElen (by decide)]; exact h.hL)
      h.el h.L1 (by omega) (h.e.congrK (i₁.trans i₂) (k₁.trans k₂)))
      fun t₃ ⟨hg₃, hY₃, f₃, k₃⟩ => ?_)
  have x₃ := Fixed.of_frm f₃ (expPhaseRanges_fixed _)
  have i₃ := InScr.of_frm f₃ (hZs (expPhaseRanges_le _))
  have x₁₃ := x₁₂.trans x₃
  have k₁₃ := (k₁.trans k₂).trans k₃
  have hM₃ : word t₃.mem B (8 * sMask) = mask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) := by
    rw [f₃.ep_hdr (by decide) (by decide) (by decide) (by decide),
      f₂.word_eq (r2Ranges_hdr _ (by decide) (by decide)) (by unfold sMask sFn; omega)]
    exact so.mask
  refine WP.mono (outPhase_ok hg₃ hZ (by omega) (by omega) hY₃ (by rw [x₁₃ sOut (by decide)]; exact h.hO)
    (by rw [x₁₃ sK (by decide)]; exact h.hK) hM₃ (fun j hj => by rw [k₁₃.2.2]; exact h.out j hj) h.outSep)
    fun t ⟨hb, hax, hsv, hfr, k₄⟩ => ⟨?_, hax, fun i hi => by rw [hsv i hi]; exact x₁₃ i (by omega),
      fun x hx hx' => by rw [hfr x hx', i₃ x hx, i₂ x hx, i₁ x hx], (k₁₃.trans k₄).mono (by decide)⟩
  rw [hb]
  by_cases hc : Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb <;> simp [hc]

end VG.Proof.Bignum.X86_64
