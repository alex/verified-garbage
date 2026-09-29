import VerifiedGarbage.Proof.MlKem.AArch64.KgB

/-!
# ML-KEM-768 on AArch64: `vg_mlkem768_keygen`, the calls of phase C

Untrusted: everything here is checked by Lean. Each building block of the
computation of `ŝ`, `ê` and `t̂` (`kgCbdNtt`, `kgEnc`, `kgMul`, `kgAdd`): what
it needs, what it computes, what it keeps (`KB`), and the only memory it
changes (`Frame`), so that the facts established before it survive it.
-/

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

/-- The offsets of `scratch`, unfolded. -/
macro "offs" : tactic => `(tactic| simp -failIfUnchanged only [kL, KG.ST, KG.WK, KG.SB, KG.SG, KG.B3,
  KG.PB, KG.SS, KG.NS, KG.AH, KG.SH, KG.EP, KG.TP, KG.PP, KG.SV, aOff, sOff])

/-- Two buffers are apart: in different arguments, or at offsets apart. -/
macro "rdisj" : tactic => `(tactic|
  exact R.disj (‹Pre _›).args (by decide) (by decide) (by offs; omega) (by offs; omega) (by offs; omega))

/-- A buffer is apart from the stack below the stack pointer. -/
macro "rbelow" : tactic => `(tactic| exact below_R ‹Pre _› (by decide) (by offs; omega))

example {s₀ : State} (hp : Pre s₀) : (R (kA s₀) 3 SG 32).Disjoint (R (kA s₀) 3 (SG + 32) 1) := by rdisj
example {s₀ : State} (hp : Pre s₀) (off : Nat) (h1 : 4128 ≤ off) (h2 : off + 1024 ≤ 19488) :
    (R (kA s₀) 3 off 1024).Disjoint (R (kA s₀) 3 NS 1024) := by rdisj

/-- A polynomial buffer in `scratch` for phase C: past `Â`'s start, below
the saved registers. -/
def PolyOff (off : Nat) : Prop := AH ≤ off ∧ off + 1024 ≤ SV

/-- What `kgCbdNtt` writes. -/
abbrev cnW (s₀ : State) (off : Nat) : List Region :=
  [R (kA s₀) 3 ST 200, R (kA s₀) 3 WK 640, below s₀.sp 16, R (kA s₀) 3 (SG + 32) 1, R (kA s₀) 3 PB 128,
    R (kA s₀) 3 off 1024, R (kA s₀) 3 NS 1024]

/-- `SamplePolyCBD₂(PRF₂(σ, N))`. -/
theorem cbdNtt_ok {s₀ : State} (hp : Pre s₀) {N off : Nat} (hN : N < 256) (ho : PolyOff off) {s : State}
    (hk : KB s₀ s) (hs : bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 SG) 32 = kgSigma (dB s₀)) :
    WP isa (kgCbdNtt N off) s fun s' => KB s₀ s' ∧ Frame (cnW s₀ off) s.mem s'.mem ∧
      PolyIs s'.mem (kA s₀ 3 + BitVec.ofNat 64 off) (ntt (cbd (kgSigma (dB s₀)) N)) := by
  have e : ∀ {u : State}, KB s₀ u → ∀ o, u.gpr .x28 + BitVec.ofNat 64 o = kA s₀ 3 + BitVec.ofNat 64 o :=
    fun hu o => by rw [hu.x28]
  obtain ⟨ho1, ho2⟩ := ho
  have ho1' : 4128 ≤ off := ho1
  have ho2' : off + 1024 ≤ 19488 := ho2
  have fo : off + 1024 ≤ kL 3 := by simp only [kL, SV] at *; omega
  -- `N` after `σ`
  refine WP.seq (wp_movz fun s₁ h₁ e₁ => wp_strb (a := kA s₀ 3 + BitVec.ofNat 64 (SG + 32)) (by decide)
    (by rw [h₁.get .x28, e hk]) (by
      rw [h₁.wr]; exact in_R (cov_w hp hk (b := 3) (o := SG + 32) (l := 1) (by decide) (by decide))
        (k := 0) (by decide) (by decide)) fun s₂ h₂ => wp_nil ?_)
  have m₂ : s₂.mem = s.mem.writeW (kA s₀ 3 + BitVec.ofNat 64 (SG + 32)) ((s₁.gpr .x9).setWidth 8) := by
    rw [h₂.mem, h₁.mem]
  have f₂ : Frame [R (kA s₀) 3 (SG + 32) 1] s.mem s₂.mem := by
    rw [m₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (R.contains (k := 0) (by decide)
      (by decide))
  have kb₂ : KB s₀ s₂ := hk.frame (h₁.keep.trans h₂.keep) f₂ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact kb_disj hp (by decide) (by decide) (by decide) (by decide)
  have msg : bytesAt s₂.mem (kA s₀ 3 + BitVec.ofNat 64 SG) 33 = kgSigma (dB s₀) ++ [BitVec.ofNat 8 N] := by
    rw [show 33 = 32 + 1 from rfl, bytesAt_add, bytesAt_frame (p := kA s₀ 3 + BitVec.ofNat 64 SG) (len := 32)
      f₂ (fun r hr => by
        rw [List.mem_singleton.mp hr]
        show (R (kA s₀) 3 SG 32).Disjoint (R (kA s₀) 3 (SG + 32) 1)
        rdisj) (by decide), hs]
    refine congrArg (kgSigma (dB s₀) ++ ·) (bytesAt_eq rfl fun k hk' => ?_)
    have : k = 0 := by omega
    subst this
    rw [ptr_zero, ptr_add, m₂, writeW8_apply, ite_eq_left rfl, e₁]
    exact sfx8 hN
  -- `PRF₂(σ, N)`
  refine WP.seq (WP.mono (hash_ok (hsetup hp kb₂ (by decide : 136 ∈ Spec.Sha3.rates)) (sfx := 0x1f)
    (by decide) (ins := [⟨.x28, SG, 33⟩]) (outs := [⟨.x28, PB, 128⟩]) (by simp)
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (b := 3) hp kb₂ (by decide) (by decide) (by decide) (by decide) (by decide))
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (b := 3) hp kb₂ (by decide) (by decide) (by decide) (by decide) (by decide))
    (List.pairwise_singleton _ _)) fun s₃ ⟨k₃, o₃⟩ => ?_)
  have kb₃ : KB s₀ s₃ := kb₂.hash hp k₃ fun p hp' => by
    rw [List.mem_singleton.mp hp']; exact ⟨3, PB, 128, rfl, by decide, by decide, by decide, by decide⟩
  have prf₃ : bytesAt s₃.mem (kA s₀ 3 + BitVec.ofNat 64 PB) 128 = prf 2 (kgSigma (dB s₀)) (BitVec.ofNat 8 N) := by
    obtain ⟨o, -⟩ := o₃
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      e kb₂] at o
    rw [msg] at o
    rw [o, prf_eq]; rfl
  have k₃' := k₃
  simp only [VG.Proof.MlKem.AArch64.STr, VG.Proof.MlKem.AArch64.WKr, preg, List.map_cons, List.map_nil,
    kb₂.x28, kb₂.sp] at k₃'
  -- `SamplePolyCBD₂`
  refine WP.seq (WP.seq (wp_ptrTo (by decide) (by decide) fun s₄ h₄ e₄ => wp_ptrTo' (by decide)
    (by simp only [SV] at ho2; omega) fun s₅ h₅ e₅ => ?_))
  have kb₅ := kb₃.block (h₄.trans h₅).keep (by rw [h₅.mem, h₄.mem]) (by decide)
  refine cbd2_call (b := kA s₀ 3 + BitVec.ofNat 64 PB) (f := kA s₀ 3 + BitVec.ofNat 64 off)
    (by rw [h₅.get .x0, e₄, e kb₃]) (by rw [e₅, h₄.get .x28, e kb₃])
    (by show (R (kA s₀) 3 PB 128).Disjoint (R (kA s₀) 3 off 1024); rdisj)
    (covers_cons (cov_r hp kb₅ (b := 3) (o := PB) (l := 128) (by decide) (by decide))
      (cov_r hp kb₅ (b := 3) (by decide) fo))
    (cov_w hp kb₅ (b := 3) (by decide) fo) fun s₆ k₆ p₆ => ?_
  have kb₆ := kb₅.call k₆ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact kb_disj hp (by decide) fo (by simp only [SV] at *; omega) (by decide)
  rw [show s₅.mem = s₃.mem by rw [h₅.mem, h₄.mem], prf₃] at p₆
  -- the NTT
  refine WP.seq (wp_ptrTo (by decide) (by simp only [SV] at ho2; omega) fun s₇ h₇ e₇ => wp_ptrTo'
    (by decide) (by decide) fun s₈ h₈ e₈ => ?_)
  have kb₈ := kb₆.block (h₇.trans h₈).keep (by rw [h₈.mem, h₇.mem]) (by decide)
  refine ntt_call (f := kA s₀ 3 + BitVec.ofNat 64 off) (w := kA s₀ 3 + BitVec.ofNat 64 NS)
    (by rw [h₈.get .x0, e₇, e kb₆]) (by rw [e₈, h₇.get .x28, e kb₆])
    (by show (R (kA s₀) 3 off 1024).Disjoint (R (kA s₀) 3 NS 1024); rdisj)
    (by rw [h₈.mem, h₇.mem]; exact p₆.1)
    (covers_cons (cov_w hp kb₈ (b := 3) (by decide) fo) (cov_w hp kb₈ (b := 3) (o := NS) (l := 1024)
      (by decide) (by decide))) fun s₉ k₉ p₉ => ?_
  have kb₉ := kb₈.call k₉ fun r hr => by
    rcases mem2' hr with rfl | rfl
    · exact kb_disj hp (by decide) fo (by simp only [SV] at *; omega) (by decide)
    · exact kb_disj hp (by decide) (by decide) (by decide) (by decide)
  have m₈ : s₈.mem = s₆.mem := by rw [h₈.mem, h₇.mem]
  have m₅ : s₅.mem = s₃.mem := by rw [h₅.mem, h₄.mem]
  have F₁ : Frame (cnW s₀ off) s.mem s₂.mem := f₂.mono fun r hr => by
    rw [List.mem_singleton.mp hr]; simp
  have F₂ : Frame (cnW s₀ off) s₂.mem s₃.mem := k₃'.frame.mono fun r hr => by
    rcases mem4 hr with rfl | rfl | rfl | rfl <;> simp
  have F₃ : Frame (cnW s₀ off) s₅.mem s₆.mem := k₆.frame.mono fun r hr => by
    rw [List.mem_singleton.mp hr]; simp
  have F₄ : Frame (cnW s₀ off) s₈.mem s₉.mem := k₉.frame.mono fun r hr => by
    rcases mem2' hr with rfl | rfl <;> simp
  rw [m₅] at F₃
  rw [m₈] at F₄
  have pv : polyAt s₈.mem (kA s₀ 3 + BitVec.ofNat 64 off) = cbd (kgSigma (dB s₀)) N := by
    rw [m₈]; exact p₆.2
  rw [pv] at p₉
  exact ⟨kb₉, F₁.trans (F₂.trans (F₃.trans F₄)), p₉⟩

end VG.Proof.MlKem.AArch64.KeyGen
