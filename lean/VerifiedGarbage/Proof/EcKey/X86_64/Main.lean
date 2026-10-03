import VerifiedGarbage.Proof.EcKey.X86_64.Middle
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Framework.X86_64.Inline

/-!
# Elliptic curve public keys on x86-64: the whole function

`publicKey_ok`: `Cfg.publicKey` computes the specification's public key of
`d`, for any curve the ECDSA proof supports (`CfgOk`), and restores the
callee-saved registers.

After `args`, the code up to `Z^(p-2)` is the signature's, with `k`, `d`
and the hash all `d`; its proof (`stage₁`, `stage₂`) is for the signature's
arguments, whose regions are within the public key's: so it runs on the
state with the signature's regions, and `Exec.widen` gives the same run
with the public key's. `middle_ok` and `publicKey_eq` do the rest.
-/

namespace VG.Proof.EcKey.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

variable {c : Cfg}

/-- The arguments: `out = rdi` (`1 + 16 n` bytes), `d = rsi` (`8 n` bytes)
and `scratch = rdx`, readable and writable as the contract says and apart
from each other as it says. -/
structure PkPre (c : Cfg) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .rsi, 8 * c.n⟩]
  wr : s.wr = [⟨s.gpr .rdi, 1 + 16 * c.n⟩, ⟨s.gpr .rdx, size⟩]
  out_sc : Region.Disjoint ⟨s.gpr .rdi, 1 + 16 * c.n⟩ ⟨s.gpr .rdx, size⟩
  out_d : Region.Disjoint ⟨s.gpr .rdi, 1 + 16 * c.n⟩ ⟨s.gpr .rsi, 8 * c.n⟩
  d_sc : Region.Disjoint ⟨s.gpr .rsi, 8 * c.n⟩ ⟨s.gpr .rdx, size⟩
  out_fit : (s.gpr .rdi).toNat + (1 + 16 * c.n) ≤ 2 ^ 64
  sc_fit : (s.gpr .rdx).toNat + size ≤ 2 ^ 64

/-- The private key. -/
abbrev dk (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rsi) (8 * c.n))

/-- The result the contract asks for: the specification's public key of `d`,
`04 ‖ x ‖ y`, and `1`, or zeros and `0`. -/
def PkPost (c : Cfg) (s₀ s' : State) : Prop :=
  match Spec.EcKey.publicKey c.C (dk c s₀) with
  | some (.affine x y) => (s'.gpr .rax).setWidth 32 = 1 ∧
      Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .rdi) (1 + 16 * c.n) = Spec.EcKey.encodePoint (.affine x y)
  | _ => (s'.gpr .rax).setWidth 32 = 0 ∧
      Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .rdi) (1 + 16 * c.n) = List.replicate (1 + 16 * c.n) 0

theorem args_ok (s : State) :
    WP isa (.block Impl.EcKey.X86_64.Cfg.args) s fun s' =>
      s'.gpr .r8 = s.gpr .rdx ∧ s'.gpr .rcx = s.gpr .rsi ∧ s'.gpr .rdx = s.gpr .rsi ∧
        Keeps [.r8, .rcx, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [Impl.EcKey.X86_64.Cfg.args, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, RegUpd.gpr_setReg, ite_true, reduceCtorEq, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]

theorem toM_eq_zero_iff {m R x : Nat} (hR : Nat.Coprime R m) (hx : x < m) : toM m R x = 0 ↔ x = 0 := by
  unfold toM
  constructor
  · intro h
    have hu : (R : ZMod m) * (R : ZMod m)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one R hR
    have h' : (x : ZMod m) = 0 := by
      have e := congrArg (· * (R : ZMod m)) h
      simp only [zero_mul] at e
      rwa [mul_assoc, mul_comm _ (R : ZMod m), hu, mul_one] at e
    exact Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff _ _).mp h') hx
  · rintro rfl
    rw [Nat.cast_zero, zero_mul]

/-- `vg_ec_<curve>_public_key` computes the specification's public key and
restores the callee-saved registers. -/
theorem publicKey_ok (hc : CfgOk c) {s₀ : State} (hp : PkPre c s₀) :
    WP isa (Impl.EcKey.X86_64.Cfg.publicKey c) s₀ fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ PkPost c s₀ s' := by
  have h0 := hc.n0
  have : Fact c.C.p.Prime := ⟨hc.good.prime⟩
  have hpR := coprime_pow_two hc.p_odd (64 * c.n)
  refine WP.seq (WP.mono (args_ok s₀) fun s₁ ⟨r8₁, rcx₁, rdx₁, k₁⟩ => ?_)
  have rsi₁ : s₁.gpr .rsi = s₀.gpr .rsi := k₁.1 _ (by decide)
  have rdi₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.1 _ (by decide)
  -- The signature's regions, `k`, `d` and the hash all at `d`.
  obtain ⟨sN, hsN⟩ : ∃ sN, sN = s₁.withRegions
      [⟨s₀.gpr .rsi, 8 * c.n⟩, ⟨s₀.gpr .rsi, 8 * c.n⟩, ⟨s₀.gpr .rsi, 8 * c.n⟩]
      [⟨s₀.gpr .rdi, 16 * c.n⟩, ⟨s₀.gpr .rdx, size⟩] := ⟨_, rfl⟩
  have g : ∀ r, sN.gpr r = s₁.gpr r := fun r => by rw [hsN]; rfl
  have mN : sN.mem = s₀.mem := by rw [hsN]; exact k₁.2.1
  have hsub : Region.Sub ⟨s₀.gpr .rdi, 16 * c.n⟩ ⟨s₀.gpr .rdi, 1 + 16 * c.n⟩ := Region.sub_prefix (by omega)
  have hpN : Pre c sN := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [g, rsi₁, rdi₁, rdx₁, rcx₁, r8₁]
    · rw [hsN]; rfl
    · rw [hsN]; rfl
    · exact hp.out_sc.sub_left hsub
    · exact hp.out_d.sub_left hsub
    · exact hp.out_d.sub_left hsub
    · exact hp.out_d.sub_left hsub
    · exact hp.d_sc
    · exact hp.d_sc
    · exact hp.d_sc
    · have := hp.out_fit; omega
    · exact hp.sc_fit
  have hb : sN.gpr .r8 = s₀.gpr .rdx := by rw [g, r8₁]
  obtain ⟨t, s₂N, ex, S₂⟩ := stage₁ hc hpN (rest := .seq (ladder c.ladderCfg) (.seq (pow c.powP) (.block [])))
    (Q := St₂ c sN (sN.gpr .r8)) fun _ S₁ => stage₂ hc S₁ fun _ S₂ => WP.block_nil S₂
  rw [hb] at S₂
  -- The same run, with the public key's regions.
  have hrd₁ : s₁.rd = [⟨s₀.gpr .rsi, 8 * c.n⟩] := by rw [k₁.2.2.1, hp.rd]
  have hwr₁ : s₁.wr = [⟨s₀.gpr .rdi, 1 + 16 * c.n⟩, ⟨s₀.gpr .rdx, size⟩] := by rw [k₁.2.2.2, hp.wr]
  have ex' := Exec.widen ex (rd := s₁.rd) (wr := s₁.wr)
    (by
      rw [hsN, State.withRegions_rd, State.withRegions_wr, hrd₁, hwr₁]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., 0, (BitVec.add_zero _).symm, Nat.le_of_eq (Nat.zero_add _)⟩
      · exact ⟨_, List.mem_cons_self .., 0, (BitVec.add_zero _).symm, Nat.le_of_eq (Nat.zero_add _)⟩
      · exact ⟨_, List.mem_cons_self .., 0, (BitVec.add_zero _).symm, Nat.le_of_eq (Nat.zero_add _)⟩
      · exact ⟨⟨s₀.gpr .rdi, 1 + 16 * c.n⟩, by simp, 0, (BitVec.add_zero _).symm,
          by show 0 + 16 * c.n ≤ 1 + 16 * c.n; omega⟩
      · exact ⟨⟨s₀.gpr .rdx, size⟩, by simp, 0, (BitVec.add_zero _).symm, Nat.le_of_eq (Nat.zero_add _)⟩)
    (by
      rw [hsN, State.withRegions_wr, hwr₁]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨s₀.gpr .rdi, 1 + 16 * c.n⟩, List.mem_cons_self .., 0, (BitVec.add_zero _).symm,
          by show 0 + 16 * c.n ≤ 1 + 16 * c.n; omega⟩
      · exact ⟨⟨s₀.gpr .rdx, size⟩, by simp, 0, (BitVec.add_zero _).symm, Nat.le_of_eq (Nat.zero_add _)⟩)
  rw [hsN, State.withRegions_withRegions, State.withRegions_self] at ex'
  obtain ⟨s₂, hs₂⟩ : ∃ s₂, s₂ = s₂N.withRegions s₁.rd s₁.wr := ⟨_, rfl⟩
  rw [← hs₂] at ex'
  have g₂ : s₂.gpr = s₂N.gpr := by rw [hs₂]; rfl
  have m₂ : s₂.mem = s₂N.mem := by rw [hs₂]; rfl
  have w₂ : s₂.wr = s₁.wr := by rw [hs₂]; rfl
  have sv₂ : ∀ i, sv c (s₀.gpr .rdx) s₂ i = sv c (s₀.gpr .rdx) s₂N i := fun i => by rw [sv, sv, m₂]
  have hs₂' : Scr s₂ (s₀.gpr .rdx) size :=
    ⟨by rw [g₂]; exact S₂.scr.rdi, by rw [w₂, hwr₁]; simp, S₂.scr.nowrap⟩
  have F₂ : Fixed c (s₀.gpr .rdx) sN.gpr s₂.mem := m₂ ▸ S₂.fixed
  obtain ⟨t', s', exm, xv, yv, hxl, hx, hyl, hy, bytes, rax, saved⟩ :=
    middle_ok hc hs₂' F₂ (by rw [sv₂]; exact S₂.acc_lt) (by rw [m₂]; exact S₂.flag)
      (by rw [g₂, S₂.r14, g, rdi₁]) (by rw [w₂, hwr₁]; simp) hp.out_sc
  refine ⟨_, _, .seq ex' exm, fun r hr => ?_, ?_⟩
  · have hsv : ∀ r ∈ Cfg.saved.map Prod.fst, r ∉ [Reg.r8, .rcx, .rdx] := by decide
    rw [saved r hr, g, k₁.1 r (hsv r hr)]
  -- The specification.
  have hk : kv c sN = dk c s₀ := by simp only [kv, dk, mN, g, rcx₁]
  have hD : sv c (s₀.gpr .rdx) s₂ D = dk c s₀ := by rw [sv₂, S₂.d]; simp only [dv, dk, mN, g, rsi₁]
  have hR := S₂.rep
  rw [hk] at hR
  have hZ : ∀ {i}, tmv c.C c.n (s₀.gpr .rdx) s₂N (c.sl i) = toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .rdx) s₂ i) :=
    fun {i} => by rw [sv₂]
  have acc := S₂.acc
  rw [← sv₂, hZ] at acc
  rw [hZ, hZ, hZ] at hR
  have hxX : (xv : ZMod c.C.p) = toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .rdx) s₂ RX) *
      toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .rdx) s₂ RZ) ^ (c.C.p - 2) := by rw [hx, acc]
  have hyY : (yv : ZMod c.C.p) = toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .rdx) s₂ RY) *
      toM c.C.p (2 ^ (64 * c.n)) (sv c (s₀.gpr .rdx) s₂ RZ) ^ (c.C.p - 2) := by rw [hy, acc]
  have hz := toM_eq_zero_iff hpR (x := sv c (s₀.gpr .rdx) s₂ RZ) (by rw [sv₂]; exact S₂.rz_lt)
  unfold PkPost
  rw [publicKey_eq hR hxl hxX hyl hyY]
  by_cases hd : 1 ≤ dk c s₀ ∧ dk c s₀ < c.C.n
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hd)]
    by_cases h0 : sv c (s₀.gpr .rdx) s₂ RZ = 0
    · have hok : ok c (s₀.gpr .rdx) s₂ = false := decide_eq_false (by rw [hD]; omega)
      rw [ite_eq_left_of_eq_true _ _ (eq_true (hz.mpr h0))]
      exact ⟨by rw [rax, hok]; rfl, by rw [bytes, hok]; rfl⟩
    · have hok : ok c (s₀.gpr .rdx) s₂ = true := decide_eq_true (by rw [hD]; omega)
      rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => h0 (hz.mp h)))]
      refine ⟨by rw [rax, hok]; rfl, ?_⟩
      rw [bytes, hok]
      show _ = 4 :: (toBytes c.C.len xv ++ toBytes c.C.len yv)
      rw [hc.len]; rfl
  · have hok : ok c (s₀.gpr .rdx) s₂ = false := decide_eq_false (by rw [hD]; omega)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]
    exact ⟨by rw [rax, hok]; rfl, by rw [bytes, hok]; rfl⟩

end VG.Proof.EcKey.X86_64
