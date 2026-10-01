import VerifiedGarbage.Proof.Blake2.X86.CompressB.G

/-!
# BLAKE2b on x86 (32-bit): the rounds

Untrusted: everything here is checked by Lean. `G_step` moves `g_ok` to the
work vector (`Holds`), for any four of its words; `round_ok` composes the
eight `G`s of a round, for any round, and `rounds_ok` the rounds.
-/

namespace VG.Proof.Blake2.X86.CompressB

open VG VG.X86
open VG.Impl.Blake2.X86.CompressB (vOff msgOff g gAt round rounds)
open VG.Proof.Sha512.X86 (Acc rd64)
open VG.Spec.Blake2 (Work Block G)
open VG.Proof.Blake2 (mix G_get)

/-- The work vector `v` is in `scratch[128..256)` (at `B`). -/
def Holds (B : BitVec 32) (v : Work 64) (m : Mem) : Prop :=
  ∀ k (hk : k < 16), rd64 m B (vOff k) = v[k]

/-- The block `M` is in `scratch[0..128)` (at `B`). -/
def Msg (B : BitVec 32) (M : Block 64) (m : Mem) : Prop :=
  ∀ j : Fin 16, rd64 m B (msgOff j) = M j

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (B : BitVec 32) (M : Block 64) (v : Work 64) (s₀ s : State) : Prop where
  holds : Holds B v s.mem
  msg : Msg B M s.mem
  keep : Keep s₀ s
  frame : Frame [⟨B.setWidth 64, 256⟩] s₀.mem s.mem

theorem vOff_sep {j k : Nat} (_hj : j < 16) (_hk : k < 16) (h : j ≠ k) : Sep8 (vOff j) (vOff k) := by
  simp only [Sep8, vOff]; omega

theorem msg_vOff (j : Fin 16) {k : Nat} : Sep8 (msgOff j) (vOff k) := by
  have := j.2; simp only [Sep8, msgOff, vOff]; omega

/-- The side conditions of `G_step`, decidable for concrete arguments: the
four words are distinct. -/
def QSide (a b c d : Nat) : Bool := [a, b, c, d].Nodup

theorem G_step {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32) {s₀ : State}
    (h0 : s₀.gpr .esi = B) (hA : Acc s₀.wr B 512) {a b c d : Fin 16} (hq : QSide a b c d = true)
    {M : Block 64} {v : Work 64} {s : State} (hR : RI B M v s₀ s) (j k : Fin 16) :
    WP isa (.block (g (vOff a) (vOff b) (vOff c) (vOff d) (msgOff j) (msgOff k))) s
      (RI B M (G Spec.Blake2.b v a b c d (M j) (M k)) s₀) := by
  have nd : (a.1 ≠ b.1 ∧ a.1 ≠ c.1 ∧ a.1 ≠ d.1) ∧ (b.1 ≠ c.1 ∧ b.1 ≠ d.1) ∧ c.1 ≠ d.1 := by
    simpa [QSide] using hq
  obtain ⟨⟨nab, nac, nad⟩, ⟨nbc, nbd⟩, ncd⟩ := nd
  have hv : ∀ q : Fin 16, vOff q + 8 ≤ 256 := fun q => by have := q.2; simp only [vOff]; omega
  have hm : ∀ q : Fin 16, msgOff q + 8 ≤ 256 := fun q => by have := q.2; simp only [msgOff]; omega
  refine WP.mono (g_ok hfit (hv a) (hv b) (hv c) (hv d) (hm j) (hm k)
    (vOff_sep a.2 b.2 nab) (vOff_sep a.2 c.2 nac) (vOff_sep a.2 d.2 nad) (vOff_sep b.2 c.2 nbc)
    (vOff_sep b.2 d.2 nbd) (vOff_sep c.2 d.2 ncd) (msg_vOff k) (msg_vOff k)
    (hR.keep.esi h0) (hR.keep.acc hA)) fun s' ⟨hk, ea, eb, ec, ed, other, hf⟩ => ?_
  have ra := hR.holds a a.2
  have rb := hR.holds b b.2
  have rc := hR.holds c c.2
  have rd := hR.holds d d.2
  have rj := hR.msg j
  have rk := hR.msg k
  rw [ra, rb, rc, rd, rj, rk] at ea eb ec ed
  refine ⟨fun q hq => ?_, fun i => ?_, hR.keep.trans hk, hR.frame.trans hf⟩
  · rw [G_get Spec.Blake2.b v nab nac nad nbc nbd ncd _ _ q hq]
    by_cases eqb : b.1 = q
    · subst eqb; simp only [ite_true]; exact eb
    by_cases eqc : c.1 = q
    · subst eqc; simp only [eqb, ite_true, ite_false]; exact ec
    by_cases eqd : d.1 = q
    · subst eqd; simp only [eqb, eqc, ite_true, ite_false]; exact ed
    by_cases eqa : a.1 = q
    · subst eqa; simp only [eqb, eqc, eqd, ite_true, ite_false]; exact ea
    simp only [eqb, eqc, eqd, eqa, ite_false]
    rw [other _ (by simp only [vOff]; omega) (vOff_sep a.2 hq eqa) (vOff_sep b.2 hq eqb)
      (vOff_sep c.2 hq eqc) (vOff_sep d.2 hq eqd)]
    exact hR.holds q hq
  · rw [other _ (by have := i.2; simp only [msgOff]; omega) (msg_vOff i).symm (msg_vOff i).symm
      (msg_vOff i).symm (msg_vOff i).symm]
    exact hR.msg i

theorem round_ok {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32) {s₀ : State}
    (h0 : s₀.gpr .esi = B) (hA : Acc s₀.wr B 512) {M : Block 64} {v : Work 64} {s : State}
    (hR : RI B M v s₀ s) (r : Nat) :
    WP isa (round r) s (RI B M (Spec.Blake2.round Spec.Blake2.b M v r) s₀) := by
  unfold round gAt
  refine WP.seq (WP.mono (G_step hfit h0 hA (a := 0) (b := 4) (c := 8) (d := 12) (by decide) hR
    (Spec.Blake2.sigmaAt r 0) (Spec.Blake2.sigmaAt r 1)) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (G_step hfit h0 hA (a := 1) (b := 5) (c := 9) (d := 13) (by decide) h₁
    (Spec.Blake2.sigmaAt r 2) (Spec.Blake2.sigmaAt r 3)) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (G_step hfit h0 hA (a := 2) (b := 6) (c := 10) (d := 14) (by decide) h₂
    (Spec.Blake2.sigmaAt r 4) (Spec.Blake2.sigmaAt r 5)) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (G_step hfit h0 hA (a := 3) (b := 7) (c := 11) (d := 15) (by decide) h₃
    (Spec.Blake2.sigmaAt r 6) (Spec.Blake2.sigmaAt r 7)) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (G_step hfit h0 hA (a := 0) (b := 5) (c := 10) (d := 15) (by decide) h₄
    (Spec.Blake2.sigmaAt r 8) (Spec.Blake2.sigmaAt r 9)) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (G_step hfit h0 hA (a := 1) (b := 6) (c := 11) (d := 12) (by decide) h₅
    (Spec.Blake2.sigmaAt r 10) (Spec.Blake2.sigmaAt r 11)) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (G_step hfit h0 hA (a := 2) (b := 7) (c := 8) (d := 13) (by decide) h₆
    (Spec.Blake2.sigmaAt r 12) (Spec.Blake2.sigmaAt r 13)) fun s₇ h₇ => ?_)
  exact WP.mono (G_step hfit h0 hA (a := 3) (b := 4) (c := 9) (d := 14) (by decide) h₇
    (Spec.Blake2.sigmaAt r 14) (Spec.Blake2.sigmaAt r 15)) fun _ h => h

theorem rounds_ok {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32) {s₀ : State}
    (h0 : s₀.gpr .esi = B) (hA : Acc s₀.wr B 512) {M : Block 64} {v : Work 64}
    (hR : RI B M v s₀ s₀) :
    ∀ n, WP isa (rounds n) s₀ (RI B M ((List.range n).foldl (Spec.Blake2.round Spec.Blake2.b M) v) s₀)
  | 0 => WP.block_nil hR
  | n + 1 => by
    refine WP.seq (WP.mono (rounds_ok hfit h0 hA hR n) fun s h => ?_)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact round_ok hfit h0 hA h n

end VG.Proof.Blake2.X86.CompressB
