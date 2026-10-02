import VerifiedGarbage.Impl.Ed25519.Arm.ScalarMulAdd
import VerifiedGarbage.Proof.Ed25519.Arm.Field
import VerifiedGarbage.Proof.X25519.Arm.AddSub

/-! Exact full-width addition, without the field multiplier's modulo-p tail. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

variable {b : BitVec 32}

theorem scalarAddPass_ok {x y : Nat} (hx : x + 64 ≤ 4096) (hy : y + 64 ≤ 4096)
    (hxy : x = y ∨ x + 64 ≤ y ∨ y + 64 ≤ x)
    {s : State} (hc : Ctx b s) (hlx : Lim s.mem (State.addr b) x) (hly : Lim s.mem (State.addr b) y)
    {cin : Nat} (hcin : cin < 65536) (h5 : (s.gpr .r5).toNat = cin) (h6 : s.gpr .r6 = mask16) :
    WP isa (.block (pass .r0 x (addSrc x y))) s
      (PassInv .r0 x s (fun k => limb s.mem (State.addr b) x k + limb s.mem (State.addr b) y k) cin 16) := by
  refine pass_ok (by decide) hx (by rw [hc.r0]; have := hc.fit; omega)
    (fun k hk => by rw [hc.r0]; exact hc.inW (by omega)) h6 h5
    (fun k hk => by have := hlx k hk; have := hly k hk; omega) hcin ?_
  intro k hk t ht
  have hct := hc.of_rest ht.rest (by decide)
  unfold addSrc
  refine ldr0_ok hct (d := x + 4 * k) (by omega) fun u hu => ?_
  refine ldr0_ok (hct.of_rest (hu.rest (ws := [.r3]) (by decide)) (by decide))
    (d := y + 4 * k) (by omega) fun v hv => ?_
  refine wp_dp (op2_reg _ _) fun w hw => WP.block_nil ?_
  have ex : (u.gpr .r3).toNat = limb s.mem (State.addr b) x k := by
    rw [hu.gpr]; exact wd_pass hc ht.frame (Or.inr (by omega)) (by omega) (by omega)
  have ey : (v.gpr .r2).toNat = limb s.mem (State.addr b) y k := by
    rw [hv.gpr, hu.mem]; exact wd_pass hc ht.frame (by omega) (by omega) (by omega)
  refine ⟨?_, (hu.rest (by decide)).trans ((hv.rest (by decide)).trans (hw.rest (by decide))),
    by rw [hw.mem, hv.mem, hu.mem]⟩
  rw [hw.gpr]
  show (v.gpr .r3 + v.gpr .r2).toNat = _
  rw [hv.other _ (by decide), toNat_add_lt (by rw [ex, ey]; have := hlx k hk; have := hly k hk; omega), ex, ey]

theorem scalarCarryPass_ok {x : Nat} (hx : x + 64 ≤ 4096)
    {s : State} (hc : Ctx b s) (hl : Lim s.mem (State.addr b) x)
    {cin : Nat} (hcin : cin < 65536) (h5 : (s.gpr .r5).toNat = cin) (h6 : s.gpr .r6 = mask16) :
    WP isa (.block (pass .r0 x (ldSrc x))) s
      (PassInv .r0 x s (limb s.mem (State.addr b) x) cin 16) := by
  refine pass_ok (by decide) hx (by rw [hc.r0]; have := hc.fit; omega)
    (fun k hk => by rw [hc.r0]; exact hc.inW (by omega)) h6 h5
    (fun k hk => by have := hl k hk; omega) hcin ?_
  intro k hk t ht
  refine WP.mono (ldSrc_ok (hc.of_rest ht.rest (by decide)) (by omega)) fun u ⟨e, ku, mu⟩ => ?_
  exact ⟨e.trans (wd_pass hc ht.frame (Or.inr (by omega)) (by omega) (by omega)), ku.mono (by decide), mu⟩

theorem scalarPass_result {x : Nat} {s t : State} {f : Nat → Nat} {cin : Nat}
    (hc : Ctx b s) (hp : PassInv .r0 x s f cin 16 t) :
    Frame [⟨State.addr b + BitVec.ofNat 64 x, 64⟩] s.mem t.mem ∧
    Lim t.mem (State.addr b) x ∧
    V t.mem (State.addr b) x + 2 ^ 256 * (t.gpr .r5).toNat = val16 f 16 + cin := by
  have outs : ∀ k < 16, limb t.mem (State.addr b) x k = out f cin k := by
    intro k hk; have he := hp.outs k hk; rwa [hc.r0] at he
  refine ⟨by have hf := hp.frame; rwa [hc.r0] at hf,
    fun k hk => by rw [outs k hk]; exact out_lt _ _ _, ?_⟩
  change val16 _ _ + _ = _
  rw [val16_congr outs, hp.r5]
  exact chain_val f cin 16

end VG.Proof.Ed25519.Arm
