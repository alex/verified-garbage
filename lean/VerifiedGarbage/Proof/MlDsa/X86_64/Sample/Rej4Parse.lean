import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Sq
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNtt

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly4_avx2`, sampling

Untrusted: everything here is checked by Lean. Each half of a seed's
sampling (`half`) runs 168 iterations of `vg_mldsa_rej_ntt_poly`'s loop
(`rnBody_ok`) on the 504 bytes of the seed's buffer, which hold bytes
`504 h` to `504 h + 503` of its output `Xb` (`G` of the seed, as
`vg_mldsa_rej_ntt_poly` squeezes it: `Xb_getD`): from `j` coefficients
sampled, it samples those of the first `504 (h + 1)` bytes (`half_ok`), and
writes only the seed's polynomial.
-/

namespace VG.Proof.MlDsa.X86_64.Rej4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample (rnBody)
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half)
open VG.Proof.MlKem.X86_64 (Keep ea_at wp_countdown add_ofNat_zero pR WP.keep ofNat64_pred)
open VG.Proof.MlKem.X86_64.S4
open VG.Proof.MlDsa.Sample (rnFold rnStep rnFold_snoc rnFold_length_le Stored stored_nil stored_frame G_eq G_length)
open VG.Proof.MlDsa.X86_64.Sample (rnBody_ok CoeffsWr)
open VG.Spec.MlKem (poly4 seed4)
open VG.Spec.MlDsa (Zq)
open VG.Proof.MlKem (xofByte xof_squeezeFrom_getElem)

/-- ML-KEM's `S4.Env`, which this function shares. -/
abbrev EnvK := VG.Proof.MlKem.X86_64.S4.Env

/-- The 1008 bytes of output of seed `k`, which `vg_mldsa_rej_ntt_poly` samples from. -/
abbrev Xb (σ : State) (k : Nat) : List Byte := Spec.MlDsa.G (B σ k) 1008

theorem Xb_getD (σ : State) (k : Nat) {p : Nat} (hp : p < 1008) : (Xb σ k).getD p 0 = xofByte (B σ k) p := by
  have e := xof_squeezeFrom_getElem (B σ k) (pos := 0) (d := 1008) hp
  rw [Nat.zero_add] at e
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [Xb, G_length]; exact hp), Option.getD_some, ← e]
  simp only [Xb, G_eq]

/-- The coefficients of seed `k` after `n` iterations. -/
abbrev Lt (σ : State) (k n : Nat) : List Zq := rnFold [] ((Xb σ k).take (3 * n))

theorem Lt_length_le (σ : State) (k n : Nat) : (Lt σ k n).length ≤ 256 := rnFold_length_le (by simp) _

theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- A byte the frame's regions are apart from is unchanged. -/
theorem frame_byte {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {R : Region} (hd : ∀ r ∈ rs, R.Disjoint r)
    {x : Addr} (hx : R.Contains x 1) : m' x = m x :=
  hf x fun r hr hc => hd r hr x hx hc

section
variable {σ : State} (hp : Pre σ)
include hp

omit hp in
/-- Polynomial `K` lies in `a`. -/
theorem sub_poly {K : Nat} (hK : K < 4) : Region.Sub (pR (poly4 (aP σ) K)) (aR σ) := Offset.sub_base _ (by omega)

/-- A part of the scratch space is apart from polynomial `K`. -/
theorem scr_poly {K : Nat} (hK : K < 4) {a n : Nat} (h : a + n ≤ 8192) :
    ∀ r ∈ [pR (poly4 (aP σ) K)], Region.Disjoint ⟨at' σ a, n⟩ r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact Region.Disjoint.sub_right (Region.Disjoint.sub_left hp.a_scr.symm (sub_scr h)) (sub_poly hK)

omit hp in
/-- Two polynomials are apart. -/
theorem poly_poly {K k : Nat} (hK : K < 4) (hk : k < 4) (hne : k ≠ K) :
    ∀ r ∈ [pR (poly4 (aP σ) K)], (VG.Proof.MlDsa.Sample.polyR (poly4 (aP σ) k)).Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint (aP σ) (d := 1024 * k) (n := 1024) (e := 1024 * K) (k := 1024) (by omega) (by omega)
    (by omega)

/-- Writes to polynomial `K` keep `Env`. -/
theorem env_poly {K : Nat} (hK : K < 4) {s s' : State} (he : EnvK σ s)
    (hf : Frame [pR (poly4 (aP σ) K)] s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15], s'.gpr r = s.gpr r) : EnvK σ s' := by
  have hsub := sub_poly (σ := σ) hK
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hg .rbx (by simp), he.rbx], by rw [hg .r12 (by simp), he.r12],
    by rw [hg .r13 (by simp), he.r13], by rw [hg .rsp (by simp), he.rsp], by rw [hg .r15 (by simp), he.r15],
    fun i hi => ?_, he.frame.trans (hf.sub fun r hr => ?_)⟩
  · rw [hf.readW (Region.contains_self _ _) (scr_poly hp hK (by simp only [oSave]; omega)) (by decide)]
    exact he.saved i hi
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨aR σ, by simp, hsub⟩

/-- Each coefficient of polynomial `K` is writable. -/
theorem coeffsWr {K : Nat} (hK : K < 4) {s : State} (he : EnvK σ s) : CoeffsWr s.wr (poly4 (aP σ) K) := by
  intro j hj
  rw [he.wr, hp.wr]
  refine ⟨aR σ, by simp, ?_⟩
  rw [VG.Proof.MlDsa.Sample.coeffAddr, poly4, Offset.add_add]
  exact Offset.contains_base _ (by omega) (by omega)

end

/-! ## A half -/

/-- At iteration `t` of half `h` of seed `K`, from `s₀`. -/
structure HAt (σ s₀ : State) (K h t : Nat) (s : State) : Prop where
  env : EnvK σ s
  rsi : s.gpr .rsi = at' σ (oBuf + 504 * K) + BitVec.ofNat 64 (3 * t)
  rdi : s.gpr .rdi = BitVec.ofNat 64 (Lt σ K (168 * h + t)).length
  rcx : s.gpr .rcx = BitVec.ofNat 64 (168 - t)
  rbp : s.gpr .rbp = poly4 (aP σ) K
  out : ∀ p < 504, s.mem (at' σ (oBuf + 504 * K + p)) = xofByte (B σ K) (504 * h + p)
  stored : Stored s.mem (poly4 (aP σ) K) (Lt σ K (168 * h + t))
  fr : Frame [pR (poly4 (aP σ) K)] s₀.mem s.mem
  kp : Keep [.rax, .rdx, .r8, .rdi, .rsi, .rcx, .rbp] s₀ s

section
variable {σ : State} (hp : Pre σ)
include hp

omit hp in
theorem hat_byte {s₀ : State} {K h t : Nat} (hh : h < 2) {s : State} (hI : HAt σ s₀ K h t s) {j : Nat}
    (hj : 3 * t + j < 504) :
    s.mem (s.gpr .rsi + BitVec.ofNat 64 j) = (Xb σ K).getD (3 * (168 * h + t) + j) 0 := by
  have e := hI.out (3 * t + j) hj
  rw [at'] at e
  rw [hI.rsi, at', Offset.add_add, Offset.add_add, e, Xb_getD σ K (by omega)]
  congr 1; omega

theorem hat_regions {s₀ : State} {K h t : Nat} (hK : K < 4) {s : State} (hI : HAt σ s₀ K h t s) {j : Nat}
    (hj : 3 * t + j < 504) :
    InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 j) 1 := by
  rw [hI.rsi, at', Offset.add_add, Offset.add_add]
  exact in_scr' hp hI.env.rd hI.env.wr (by simp only [oBuf]; omega)

/-- An iteration. -/
theorem hat_step {s₀ : State} {K h t : Nat} (hK : K < 4) (hh : h < 2) (ht : t < 168) {s : State}
    (hI : HAt σ s₀ K h t s) :
    WP isa rnBody s fun s' => HAt σ s₀ K h (t + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (168 - t) - 1 == 0) := by
  refine WP.mono (rnBody_ok s (aP := poly4 (aP σ) K) hI.rbp hI.rdi (Lt_length_le σ K _) (coeffsWr hp hK hI.env)
    hI.stored (by simpa using hat_regions hp hK hI (j := 0) (by omega)) (hat_regions hp hK hI (by omega))
    (hat_regions hp hK hI (by omega))) fun s' ⟨hdi, hst, hf, hsi, hcx, hz, hk⟩ => ?_
  have e0 := hat_byte hh hI (j := 0) (by omega)
  rw [add_ofNat_zero, Nat.add_zero] at e0
  have ht3 : Lt σ K (168 * h + (t + 1)) = rnStep (Lt σ K (168 * h + t)) ((Xb σ K).getD (3 * (168 * h + t)) 0)
      ((Xb σ K).getD (3 * (168 * h + t) + 1) 0) ((Xb σ K).getD (3 * (168 * h + t) + 2) 0) := by
    simp only [Lt]
    rw [show 3 * (168 * h + (t + 1)) = 3 * (168 * h + t) + 3 by omega,
      VG.Proof.MlDsa.X86_64.Sample.RejNtt.take_add_three _ (by rw [Xb, G_length]; omega),
      rnFold_snoc _ (by rw [List.length_take, Xb, G_length]; omega)]
  rw [e0, hat_byte hh hI (j := 1) (by omega), hat_byte hh hI (j := 2) (by omega), ← ht3] at hdi hst
  have hk' : Keep [.rax, .rdx, .r8, .rdi, .rsi, .rcx] s s' := hk
  refine ⟨⟨env_poly hp hK hI.env hf hk'.2.1 hk'.2.2 fun r hr => hk'.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [hsi, hI.rsi, Offset.add_add, show 3 * t + 3 = 3 * (t + 1) by omega], hdi,
    by rw [hcx, hI.rcx, ofNat64_pred (by omega) (by omega)]; rfl,
    by rw [hk'.gpr (by decide), hI.rbp],
    fun p hp' => by
      rw [frame_byte hf (scr_poly hp hK (a := oBuf + 504 * K + p) (n := 1) (by simp only [oBuf]; omega))
        (Region.contains_self _ _)]
      exact hI.out p hp',
    hst, hI.fr.trans hf, (hI.kp.trans hk').mono (by simp)⟩, by rw [hz, hI.rcx]⟩

/-- Before a half: what holds of seed `K`. -/
structure HPre (σ : State) (K h : Nat) (s : State) : Prop where
  env : EnvK σ s
  out : ∀ p < 504, s.mem (at' σ (oBuf + 504 * K + p)) = xofByte (B σ K) (504 * h + p)
  j : s.mem.readW (at' σ (oJ + 8 * K)) 64 = BitVec.ofNat 64 (Lt σ K (168 * h)).length
  stored : Stored s.mem (poly4 (aP σ) K) (Lt σ K (168 * h))

omit hp in
theorem sxB {K : Nat} (hK : K < 4) : BitVec.signExtend 64 (BitVec.ofNat 32 (oBuf + 504 * K)) =
    BitVec.ofNat 64 (oBuf + 504 * K) := sx_ofNat (by simp only [oBuf]; omega)

omit hp in
theorem sxP {K : Nat} (hK : K < 4) : BitVec.signExtend 64 (BitVec.ofNat 32 (1024 * K)) =
    BitVec.ofNat 64 (1024 * K) := sx_ofNat (by omega)

/-- The setup of a half: at iteration 0, from `j` kept. -/
theorem hsetup_ok {K h : Nat} (hK : K < 4) {s : State} (hI : HPre σ K h s) :
    WP isa (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * K))),
      .mov .rbp (.reg .r13), .alu .add .rbp (.imm (BitVec.ofNat 32 (1024 * K))),
      .mov .rdi (.mem (at_ .rbx (oJ + 8 * K))), .mov32 .rcx (.imm 168)]) s (HAt σ s K h 0) := by
  have hin : InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oJ + 8 * K)) 8 :=
    in_scr' hp hI.env.rd hI.env.wr (by simp only [oJ]; omega)
  refine WP.mono (WP.keep [.rsi, .rbp, .rdi, .rcx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = at' σ (oBuf + 504 * K) ∧ s'.gpr .rbp = poly4 (aP σ) K ∧
      s'.gpr .rdi = BitVec.ofNat 64 (Lt σ K (168 * h)).length ∧ s'.gpr .rcx = BitVec.ofNat 64 168)
    (by
      xrun [hI.env.rbx, hI.env.r13, sxB hK, sxP hK, hin, hI.j]
      rfl)
    rfl) fun s₁ ⟨⟨hm, hsi, hbp, hdi, hcx⟩, k₁⟩ => ?_
  exact ⟨hI.env.keep hm k₁ (by decide), by rw [hsi, add_ofNat_zero],
    by rw [hdi, Nat.add_zero], by rw [hcx], hbp, by rw [hm]; exact hI.out, by rw [hm, Nat.add_zero]; exact hI.stored,
    by rw [hm]; exact Frame.refl _ _, k₁.mono (by simp)⟩

/-- The loop of a half, from iteration 0. -/
theorem hloop_ok {s₀ : State} {K h : Nat} (hK : K < 4) (hh : h < 2) {s : State} (hI : HAt σ s₀ K h 0 s) :
    WP isa (.loop rnBody .ne) s (HAt σ s₀ K h 168) := by
  refine wp_countdown (N := 168) (by decide) (by decide) (fun t u => HAt σ s₀ K h t u)
    (fun t ht u hu _ => WP.mono (hat_step hp hK hh ht hu) fun u' ⟨hu', hz⟩ => ⟨hu', ?_, by rw [hz, hu.rcx]⟩)
    (fun _ h => h) hI hI.rcx
  rw [hu'.rcx, hu.rcx, ofNat64_pred (by omega) (by omega)]; rfl

/-- A half of seed `K`: the coefficients of the first `504 (h + 1)` bytes,
writing only polynomial `K`. -/
theorem half_ok {K h : Nat} (hK : K < 4) (hh : h < 2) {s : State} (hI : HPre σ K h s) :
    WP isa (half K) s (HAt σ s K h 168) :=
  WP.seq (WP.mono (hsetup_ok hp hK hI) fun _ h₁ => hloop_ok hp hK hh h₁)

end

end VG.Proof.MlDsa.X86_64.Rej4
