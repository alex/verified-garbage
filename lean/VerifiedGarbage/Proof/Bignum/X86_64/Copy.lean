import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Impl.Rsa.X86_64

/-!
# Multiword arithmetic on x86-64: copying words

`copyWords` copies `w` words from `rsi` to `rbx` (`copyWords_ok`), between
the working space and a buffer outside it, either way.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-- Numbers at two places with the same words. -/
theorem wv_congr2 {m m' : Mem} {p p' : Addr} {d d' n : Nat}
    (h : ∀ i < n, word m' p' (d' + 8 * i) = word m p (d + 8 * i)) : wv m' p' d' n = wv m p d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [wv]
    rw [ih fun i hi => h i (by omega), h n (by omega)]

/-- After copying `j` words from `S + eS` to `D + eD`. -/
structure CopyInv (s₀ : State) (S D : Addr) (eS eD : Nat) (j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  done : ∀ i < j, word t.mem D (eD + 8 * i) = word s₀.mem S (eS + 8 * i)
  frame : Outside D eD (8 * j) s₀.mem t.mem

theorem copyStep_ok {s₀ : State} {S D : Addr} {eS eD w : Nat}
    (hsi : s₀.gpr .rsi = off S eS) (hbx : s₀.gpr .rbx = off D eD) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (hD : eD + 8 * w ≤ 2 ^ 64)
    (hrd : ∀ j < w, InRegions (s₀.rd ++ s₀.wr) (off S (eS + 8 * j)) 8)
    (hwr : ∀ j < w, InRegions s₀.wr (off D (eD + 8 * j)) 8)
    (hsep : ∀ j < w, ∀ b < 8, ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b) < eD ∨
      eD + 8 * w ≤ ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b))
    {j : Nat} (hj : j < w) {t : State} (hI : CopyInv s₀ S D eS eD j t) :
    WP isa (.block (([.mov .rax (.mem (ix .rsi .r14)), .store (ix .rbx .r14) .rax] : List Instr) ++
        ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ CopyInv s₀ S D eS eD (j + 1) t' := by
  have tsi : t.gpr .rsi = off S eS := (hI.keep.gpr (by decide)).trans hsi
  have tbx : t.gpr .rbx = off D eD := (hI.keep.gpr (by decide)).trans hbx
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have hld : InRegions (t.rd ++ t.wr) (off S (eS + 8 * j)) 8 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hrd j hj
  have hst : InRegions t.wr (off D (eD + 8 * j)) 8 := by rw [hI.keep.2.2]; exact hwr j hj
  have hv : word t.mem S (eS + 8 * j) = word s₀.mem S (eS + 8 * j) :=
    Mem.readW_congr fun b hb => hI.frame _ (by have := hsep j hj b hb; omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off D (eD + 8 * j)) (word s₀.mem S (eS + 8 * j))) ?_ rfl)
    fun t₁ ⟨hm, k₁⟩ => ?_
  · xrun [State.ea, ix, addr0 tsi hI.r14, addr0 tbx hI.r14, hld, hst, hv]
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨((hI.keep.trans k₁).trans k').mono (by decide), h14, fun i hi => ?_, ?_⟩
  · rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [(writeW_outside t.mem D _ (by omega)).word (by omega) (by omega)]; exact hI.done i hi
    · exact word_writeW_self _ _ _ _
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem D _ (by omega) x (by omega)]
    exact hI.frame x (by omega)

/-- `copyWords`: the `w` words at `S + eS` to `D + eD`, which they do not
overlap, changing only those. -/
theorem copyWords_ok {s : State} {S D : Addr} {eS eD w : Nat}
    (hsi : s.gpr .rsi = off S eS) (hbx : s.gpr .rbx = off D eD) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hD : eD + 8 * w ≤ 2 ^ 64)
    (hrd : ∀ j < w, InRegions (s.rd ++ s.wr) (off S (eS + 8 * j)) 8)
    (hwr : ∀ j < w, InRegions s.wr (off D (eD + 8 * j)) 8)
    (hsep : ∀ j < w, ∀ b < 8, ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b) < eD ∨
      eD + 8 * w ≤ ofs D (off S (eS + 8 * j) + BitVec.ofNat 64 b)) :
    WP isa copyWords s fun t =>
      wv t.mem D eD w = wv s.mem S eS w ∧ (∀ i < w, word t.mem D (eD + 8 * i) = word s.mem S (eS + 8 * i)) ∧
      Outside D eD (8 * w) s.mem t.mem ∧ Keep [.rax, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      CopyInv s S D eS eD 0 t := fun t h14 hm k _ =>
    ⟨k.mono (by decide), h14, fun i hi => absurd hi (Nat.not_lt_zero _),
      by rw [hm]; exact Outside.refl _ _ _ _⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw' (CopyInv s S D eS eD) h0
    (fun j _ hj t hI => copyStep_ok hsi hbx h12 (by omega) hD hrd hwr hsep hj hI)) fun t hI => ?_
  exact ⟨wv_congr2 hI.done, hI.done, hI.frame, hI.keep⟩

end VG.Proof.Bignum.X86_64
