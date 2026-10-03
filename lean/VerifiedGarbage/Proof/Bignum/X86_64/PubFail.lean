import VerifiedGarbage.Proof.Bignum.X86_64.PubMain

/-!
# `vg_rsa_public` on x86-64: an invalid modulus

`fail` writes `k` zeros to `out`, returns 0 and restores the saved
registers (`fail_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64
open VG.WriteBytes (writeW8_apply)

/-- After `j` zeros from `s₀`. -/
structure FailInv (s₀ : State) (op : Addr) (k j : Nat) (t : State) : Prop where
  keep : Keep [.rsi, .rcx] s₀ t
  rsi : t.gpr .rsi = op + BitVec.ofNat 64 j
  rcx : t.gpr .rcx = BitVec.ofNat 64 (k - j)
  bytes : ∀ i < j, t.mem (op + BitVec.ofNat 64 i) = 0
  frame : ∀ x, (∀ i < j, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s₀.mem x

theorem i2osp_zero (k : Nat) : Spec.Rsa.i2osp 0 k = (List.range k).map fun _ => 0 := by
  unfold Spec.Rsa.i2osp
  simp

theorem fail_ok {s : State} {B : Addr} {Z k : Nat} {op : Addr} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : 8 * 32 ≤ Z) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hO : word s.mem B (8 * sOut) = op) (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1)
    (hsep : ∀ j < k, Z ≤ ofs B (op + BitVec.ofNat 64 j)) :
    WP isa fail s fun t => MainPost s t B Z k op 0 false := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold fail
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t => t.gpr .rsi = op ∧
      t.gpr .rcx = BitVec.ofNat 64 k ∧ t.gpr .rax = 0 ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hl sOut (by decide), hl sK (by decide), hO, hK]) rfl) fun s₁ ⟨⟨hsi, hcx, hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (wp_upto (a := 0) (N := k) (by omega) (FailInv s₁ op k) ?_ (fun t h => h)
    ⟨Keep.refl _ _, by rw [hsi, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero], by rw [hcx, Nat.sub_zero],
      fun i hi => absurd hi (by omega), fun x _ => rfl⟩) fun t₂ hI => ?_)
  · intro j _ hj t hI
    have hst : InRegions t.wr (op + BitVec.ofNat 64 j) 1 := by
      rw [hI.keep.2.2, k₁.2.2]; exact hout j hj
    have hax' : (t.gpr .rax).setWidth 8 = 0 := by rw [hI.keep.gpr (by decide), hax]; rfl
    refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t' =>
        t'.mem = t.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
        t'.gpr .rsi = op + BitVec.ofNat 64 (j + 1) ∧ t'.gpr .rcx = BitVec.ofNat 64 (k - (j + 1)) ∧
        t'.zf = some (decide (j + 1 = k))) (by
      xrun [State.ea, at0, hI.rsi, hI.rcx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hst, hax',
        ofNat64_pred (show 1 ≤ k - j by omega) (by omega), BitVec.add_assoc, ofNat_add_one,
        ofNat64_beq_zero (show k - j - 1 < 2 ^ 64 by omega)]
      exact ⟨by rw [show k - j - 1 = k - (j + 1) by omega], decide_eq_decide.mpr (by omega)⟩) rfl)
      fun t' ⟨⟨hm, hsi', hcx', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), hsi', hcx', ?_, ?_⟩
    · intro i hi
      rw [hm, writeW8_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) hij))]
        exact hI.bytes i (by omega)
    · intro x hx
      rw [hm, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
      exact hI.frame x fun i hi => hx i (by omega)
  -- The saved registers.
  have hw₂ : ∀ i < 32, word t₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    apply Mem.readW_congr
    intro b hb
    rw [hI.frame _ (fun j hj => scr_ne_out hsep (d := 8 * i) (i := b) (by omega) (by omega) j (by omega)), hm₁]
  have k12 := k₁.trans hI.keep
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi => by
    rw [k12.2.1, k12.2.2]; exact hl i hi
  have hdi₂ : t₂.gpr .rdi = B := (k12.gpr (by decide)).trans hdi
  rw [exit_eq]
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rbx = word s.mem B (8 * 0) ∧
      t.gpr .rbp = word s.mem B (8 * 1) ∧ t.gpr .r12 = word s.mem B (8 * 2) ∧
      t.gpr .r13 = word s.mem B (8 * 3) ∧ t.gpr .r14 = word s.mem B (8 * 4) ∧
      t.gpr .r15 = word s.mem B (8 * 5) ∧ t.mem = t₂.mem) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ 0 (by decide), hl₂ 1 (by decide), hl₂ 2 (by decide),
      hl₂ 3 (by decide), hl₂ 4 (by decide), hl₂ 5 (by decide), hw₂ 0 (by decide), hw₂ 1 (by decide),
      hw₂ 2 (by decide), hw₂ 3 (by decide), hw₂ 4 (by decide), hw₂ 5 (by decide)]) rfl)
    fun t ⟨⟨h0, h1, h2, h3, h4, h5, hm⟩, k₃⟩ => ⟨?_, ?_, ?_, ?_, (k12.trans k₃).mono (by decide)⟩
  · rw [i2osp_zero]
    exact List.map_congr_left fun i hi => by rw [hm]; exact hI.bytes i (List.mem_range.mp hi)
  · rw [k₃.gpr (by decide), hI.keep.gpr (by decide), hax]; rfl
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · intro x _ hx
    rw [hm, hI.frame x hx, hm₁]

end VG.Proof.Bignum.X86_64
