import VerifiedGarbage.Impl.Ed25519.Arm.Scalar
import VerifiedGarbage.Proof.Ed25519.Arm.Field
import VerifiedGarbage.Proof.X25519.Arm.Mul
import VerifiedGarbage.Impl.Ed25519.Arm.ScalarMulAdd
import VerifiedGarbage.Proof.X25519.Arm.AddSub
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarCodec
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarLoop
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarABI
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ed25519.Arm.UnpackField
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarFinish
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-! Merged from `Proof.Ed25519.Arm.ScalarMulAddEngine`. -/
section
/-! Merged from `Proof.Ed25519.Arm.ScalarWideAdd`. -/
section
/-! Merged from `Proof.Ed25519.Arm.ScalarWide`. -/
section
/-! Exact multiplication uses the field multiplier's checked row loop,
but stops before folding the high 256 bits modulo the field prime. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarWideMul_ok {b : BitVec 32} {x y : Nat}
    (hx : x + 64 ≤ ACC) (hy : y + 64 ≤ ACC) {s : State}
    (hc : Ctx b s) (hlx : Lim s.mem (State.addr b) x) (hly : Lim s.mem (State.addr b) y) :
    WP isa (scalarWideMul x y) s fun t =>
      Rest clob s t ∧ Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s.mem t.mem ∧
      (∀ k < 32, accw ACC t.mem (State.addr b) k < 65536) ∧
      val16 (accw ACC t.mem (State.addr b)) 32 = V s.mem (State.addr b) x * V s.mem (State.addr b) y := by
  unfold scalarWideMul
  refine WP.seq (WP.mono (mulPre_ok (by decide) (x := x) (y := y) hc) fun s1 h1 => ?_)
  refine WP.mono (Q := RowInv 4096 ACC b x y s 16) (WP.loop (M := isa)
    (fun n t => ∃ i, n = 16 - i ∧ i < 16 ∧ RowInv 4096 ACC b x y s i t) ?_ 16 s1
    ⟨0, rfl, by decide, h1⟩) fun t ht => ⟨ht.rest, ht.frame, ht.lt, ht.val⟩
  rintro n t ⟨i, rfl, hi, ht⟩
  refine WP.mono (row_ok (by decide) hx hy hlx hly hi ht) fun u ⟨hu, hz⟩ => ?_
  by_cases h16 : i + 1 = 16
  · refine .inl ⟨by rw [eval_ne, hz]; simp [h16], ?_⟩
    rw [h16] at hu; exact hu
  · exact .inr ⟨by rw [eval_ne, hz]; simp; omega, 16 - (i + 1), by omega,
      i + 1, rfl, by omega, hu⟩

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarAddPass`. -/
section
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
end

/-! Add the 256-bit scalar to all 512 product bits, carrying across both halves. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarWide_split (m : Mem) (b : BitVec 32) :
    val16 (accw ACC m (State.addr b)) 32 = V m (State.addr b) ACC + 2 ^ 256 * V m (State.addr b) (ACC + 64) := by
  rw [show (32 : Nat) = 16 + 16 from rfl, val16_append]
  have he : val16 (fun k => accw ACC m (State.addr b) (16 + k)) 16 = V m (State.addr b) (ACC + 64) := by
    apply val16_congr
    intro k _
    unfold accw limb
    rw [show ACC + 4 * (16 + k) = ACC + 64 + 4 * k by omega]
  rw [he]
  rfl

theorem scalarWideAdd_ok {b : BitVec 32} {r : Nat} (hr : r + 64 ≤ ACC) {s : State}
    (hc : Ctx b s) (lr : Lim s.mem (State.addr b) r)
    (la : ∀ k < 32, accw ACC s.mem (State.addr b) k < 65536) :
    WP isa (.block (scalarWideAdd r)) s fun t =>
      Rest [.r2, .r3, .r4, .r5, .r6] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s.mem t.mem ∧
      (∀ k < 32, accw ACC t.mem (State.addr b) k < 65536) ∧
      val16 (accw ACC t.mem (State.addr b)) 32 + 2 ^ 512 * (t.gpr .r5).toNat =
        val16 (accw ACC s.mem (State.addr b)) 32 + V s.mem (State.addr b) r := by
  have hA : ACC = 1472 := rfl
  have ll : Lim s.mem (State.addr b) ACC := fun k hk => la k (by omega)
  have lh : Lim s.mem (State.addr b) (ACC + 64) := by
    intro k hk
    have he : limb s.mem (State.addr b) (ACC + 64) k = accw ACC s.mem (State.addr b) (16 + k) := by
      unfold limb accw; rw [show ACC + 64 + 4 * k = ACC + 4 * (16 + k) by omega]
    rw [he]; exact la _ (by omega)
  rw [scalarWideAdd, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine wp_movw fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have k2 : Rest [.r5, .r6] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have m2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have hc2 := hc.of_rest k2 (by decide)
  refine WP.append (scalarAddPass_ok (x := ACC) (y := r) (by decide) (by omega) (Or.inr (Or.inr hr))
    hc2 (m2 ▸ ll) (m2 ▸ lr) (by decide : 0 < 65536) (by rw [u2.gpr]; rfl)
    (by rw [u2.other _ (by decide), u1.gpr])) fun s3 h3 => ?_
  obtain ⟨f3, l3, v3⟩ := scalarPass_result hc2 h3
  have hc3 := hc2.of_rest h3.rest (by decide)
  have hs3 : Lim s3.mem (State.addr b) (ACC + 64) :=
    fun k hk => by
      rw [limb_frame f3 (fun z hz j hj => by
        rw [List.mem_singleton.mp hz]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) k hk, m2]
      exact lh k hk
  have hi3 : V s3.mem (State.addr b) (ACC + 64) = V s.mem (State.addr b) (ACC + 64) := by
    apply val16_congr
    intro k hk
    rw [limb_frame f3 (fun z hz j hj => by
      rw [List.mem_singleton.mp hz]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) k hk, m2]
  have carry3 : (s3.gpr .r5).toNat < 65536 := by
    rw [h3.r5]
    exact chain_lt (fun k hk => by have := ll k hk; have := lr k hk; rw [m2]; omega)
      (by decide) 16 (Nat.le_refl _)
  refine WP.mono (scalarCarryPass_ok (x := ACC + 64) (by decide) hc3 hs3 carry3 rfl
    (by rw [h3.rest.gpr _ (by decide), u2.other _ (by decide), u1.gpr])) fun t ht => ?_
  obtain ⟨ft, lt, vt⟩ := scalarPass_result hc3 ht
  have lrt : ∀ k < 16, limb t.mem (State.addr b) ACC k = limb s3.mem (State.addr b) ACC k :=
    limb_frame ft fun z hz j hj => by
      rw [List.mem_singleton.mp hz]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  have vlo : V t.mem (State.addr b) ACC = V s3.mem (State.addr b) ACC := val16_congr lrt
  refine ⟨(k2.mono (by decide)).trans ((h3.rest.mono (by decide)).trans (ht.rest.mono (by decide))), ?_, ?_, ?_⟩
  · have f3' : Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s.mem s3.mem := by
      rw [← m2]
      exact f3.sub fun z hz => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hz]; exact Region.sub_prefix (by decide)⟩
    exact f3'.trans (ft.sub fun z hz => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hz]; exact Offset.sub _ (by decide) (by decide)⟩)
  · intro k hk
    rcases Nat.lt_or_ge k 16 with hk16 | hk16
    · rw [show accw ACC t.mem (State.addr b) k = limb t.mem (State.addr b) ACC k from rfl, lrt k hk16]
      exact l3 k hk16
    · have he : accw ACC t.mem (State.addr b) k = limb t.mem (State.addr b) (ACC + 64) (k - 16) := by
        unfold accw limb; rw [show ACC + 4 * k = ACC + 64 + 4 * (k - 16) by omega]
      rw [he]; exact lt _ (by omega)
  · rw [val16_add, Nat.add_zero, m2] at v3
    change V s3.mem (State.addr b) ACC + _ = V s.mem (State.addr b) ACC + V s.mem (State.addr b) r at v3
    change V t.mem (State.addr b) (ACC + 64) + _ = V s3.mem (State.addr b) (ACC + 64) + _ at vt
    rw [hi3] at vt
    rw [scalarWide_split, scalarWide_split, vlo]
    omega

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarPackWide`. -/
section
/-! Serialize all 512 product bits for the same checked reduction engine. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarPackWide_ok {b : BitVec 32} {s : State} (hc : Ctx b s)
    (la : ∀ k < 32, accw ACC s.mem (State.addr b) k < 65536) :
    WP isa (.block scalarPackWide) s fun t =>
      Rest [.r3, .r12] s t ∧ Frame [⟨State.addr b + BitVec.ofNat 64 512, 64⟩] s.mem t.mem ∧
      t.gpr .r12 = b + BitVec.ofNat 32 512 ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (State.addr b + BitVec.ofNat 64 512) 64) =
        val16 (accw ACC s.mem (State.addr b)) 32 := by
  have hA : ACC = 1472 := rfl
  have ll : Lim s.mem (State.addr b) ACC := fun k hk => la k (by omega)
  have lh : Lim s.mem (State.addr b) (ACC + 64) := by
    intro k hk
    change wd s.mem (State.addr b) (ACC + 64 + 4 * k) < _
    rw [show ACC + 64 + 4 * k = ACC + 4 * (16 + k) by omega]
    exact la _ (by omega)
  have afit := hc.fit
  have ep : State.addr (b + BitVec.ofNat 32 512) = State.addr b + BitVec.ofNat 64 512 :=
    addr_add (by omega)
  have pf : (b + BitVec.ofNat 32 512).toNat = b.toNat + 512 := by
    rw [toNat_add_lt (by rw [toNat_imm (by decide)]; omega), toNat_imm (by decide)]
  rw [scalarPackWide, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_imm (by decide)) fun u hu => ?_
  have hcu := hc.of_rest (hu.rest (ws := [.r12]) (by decide)) (by decide)
  have pu : u.gpr .r12 = b + BitVec.ofNat 32 512 := by rw [hu.gpr]; change s.gpr .r0 + _ = _; rw [hc.r0]; rfl
  refine WP.append (packField_ok (p := b + BitVec.ofNat 32 512) (a := ACC) (dst := 0) hcu
    (by decide) (hu.mem ▸ ll) (by decide) pu (by rw [pf]; omega)
    (fun i hi => by rw [ep, Offset.add_add]; exact hcu.inW (by omega))
    (by rw [ep, BitVec.add_zero]; exact Offset.disjoint _ (Or.inr (by decide)) (by decide) (by decide)))
    fun v ⟨kv, fv, vv⟩ => ?_
  have hcv := hcu.of_rest kv (by decide)
  have fv' : Frame [⟨State.addr b + BitVec.ofNat 64 512, 32⟩] s.mem v.mem := by
    simpa only [ep, BitVec.add_zero, hu.mem] using fv
  have hvh : ∀ k < 16, limb v.mem (State.addr b) (ACC + 64) k = limb s.mem (State.addr b) (ACC + 64) k :=
    limb_frame fv' fun r hr k hk => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (Or.inr (by omega)) (by omega) (by decide)
  have lvh : Lim v.mem (State.addr b) (ACC + 64) := fun k hk => by rw [hvh k hk]; exact lh k hk
  refine WP.mono (packField_ok (p := b + BitVec.ofNat 32 512) (a := ACC + 64) (dst := 32) hcv
    (by decide) lvh (by decide) ((kv.gpr _ (by decide)).trans pu) (by rw [pf]; omega)
    (fun i hi => by rw [ep, Offset.add_add]; exact hcv.inW (by omega))
    (by rw [ep, Offset.add_add]; exact Offset.disjoint _ (Or.inr (by decide)) (by decide) (by decide)))
    fun t ⟨kt, ft, vt⟩ => ?_
  have ft' : Frame [⟨State.addr b + BitVec.ofNat 64 544, 32⟩] v.mem t.mem := by
    simpa only [ep, Offset.add_add] using ft
  have vlo : packedV t.mem (State.addr b + BitVec.ofNat 64 512) = V s.mem (State.addr b) ACC := by
    rw [packedV_frame ft' (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (Or.inl (by decide)) (by decide) (by decide))]
    simpa only [ep, BitVec.add_zero, hu.mem] using vv
  have vhi : packedV t.mem (State.addr b + BitVec.ofNat 64 544) = V s.mem (State.addr b) (ACC + 64) := by
    have ve : V v.mem (State.addr b) (ACC + 64) = V s.mem (State.addr b) (ACC + 64) := val16_congr hvh
    simpa only [ep, Offset.add_add, ve] using vt
  refine ⟨(hu.rest (by decide)).trans ((kv.mono (by decide)).trans (kt.mono (by decide))), ?_,
    (kt.gpr _ (by decide)).trans ((kv.gpr _ (by decide)).trans pu), ?_⟩
  · exact (fv'.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).trans
      (ft'.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩)
  · change Spec.Ed25519.decodeLE (Spec.X25519.bytesAt t.mem _ (32 + 32)) = _
    rw [VG.Proof.X25519.bytesAt_add, decodeLE_append, VG.Proof.X25519.length_bytesAt]
    change Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem _ 32) +
      256 ^ 32 * Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem _ 32) = _
    rw [scalar_packed_decode, scalar_packed_decode, Offset.add_add, vlo, vhi, scalarWide_split]

end VG.Proof.Ed25519.Arm
end

/-! Full-width product plus addend, serialized and reduced modulo L. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev scalarEngineClob : List Reg := [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]
def scalarWork (b : BitVec 32) : Region := ⟨State.addr b + BitVec.ofNat 64 64, 1536⟩

theorem scalarWork_sub {b : BitVec 32} {o n : Nat} (ho : 64 ≤ o) (hn : o + n ≤ 1600) :
    (⟨State.addr b + BitVec.ofNat 64 o, n⟩ : Region).Sub (scalarWork b) :=
  Offset.sub _ ho (by omega)

theorem scalar_muladd_bound {r k a : Nat} (hr : r < 2 ^ 256) (hk : k < 2 ^ 256) (ha : a < 2 ^ 256) :
    k * a + r < 2 ^ 512 := by
  have hm : k * a ≤ (2 ^ 256 - 1) * (2 ^ 256 - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem scalar_zero_carry {n c x y : Nat} (h : x + n * c = y) (hc : c = 0) : x = y := by
  rw [hc, Nat.mul_zero, Nat.add_zero] at h
  exact h

theorem scalarMulAddEngine_ok {b : BitVec 32} {s : State} (hc : Ctx b s)
    (lr : Lim s.mem (State.addr b) 64) (lk : Lim s.mem (State.addr b) 128)
    (la : Lim s.mem (State.addr b) 192) :
    WP isa scalarMulAddEngine s fun t =>
      Rest scalarEngineClob s t ∧ Frame [scalarWork b] s.mem t.mem ∧
      Lim t.mem (State.addr b) SR ∧ V t.mem (State.addr b) SR =
        (V s.mem (State.addr b) 64 + V s.mem (State.addr b) 128 * V s.mem (State.addr b) 192) %
          Spec.Ed25519.L ∧ t.gpr .r8 = s.gpr .r10 := by
  have hA : ACC = 1472 := rfl
  unfold scalarMulAddEngine
  refine WP.seq (WP.mono (scalarWideMul_ok (by decide) (by decide) hc lk la)
    fun u ⟨ku, fu, lu, vu⟩ => ?_)
  have hcu := hc.of_rest ku (by decide)
  have ur : ∀ k < 16, limb u.mem (State.addr b) 64 k = limb s.mem (State.addr b) 64 k :=
    limb_frame fu fun z hz k hk => by
      rw [List.mem_singleton.mp hz]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  have lru : Lim u.mem (State.addr b) 64 := fun k hk => by rw [ur k hk]; exact lr k hk
  refine WP.seq (WP.append (scalarWideAdd_ok (by decide) hcu lru lu) fun v ⟨kv, fv, lv, vv⟩ => ?_)
  have hcv := hcu.of_rest kv (by decide)
  have vr : V u.mem (State.addr b) 64 = V s.mem (State.addr b) 64 := val16_congr ur
  have sum : val16 (accw ACC v.mem (State.addr b)) 32 =
      V s.mem (State.addr b) 128 * V s.mem (State.addr b) 192 + V s.mem (State.addr b) 64 := by
    rw [vu, vr] at vv
    have bound := scalar_muladd_bound (V_lt lr) (V_lt lk) (V_lt la)
    have zero : (v.gpr .r5).toNat = 0 := by
      rcases Nat.eq_zero_or_pos (v.gpr .r5).toNat with hz | hp
      · exact hz
      · have := Nat.le_mul_of_pos_right (2 ^ 512) hp; omega
    exact scalar_zero_carry vv zero
  refine WP.mono (scalarPackWide_ok hcv lv) fun w ⟨kw, fw, pw, vw⟩ => ?_
  have kr : Rest scalarEngineClob s w :=
    (ku.mono (by decide)).trans ((kv.mono (by decide)).trans (kw.mono (by decide)))
  have hcw := hc.of_rest kr (by decide)
  have pf : (b + BitVec.ofNat 32 512).toNat + 64 ≤ 2 ^ 32 := by
    rw [toNat_add_lt (by rw [toNat_imm (by decide)]; have := hc.fit; omega), toNat_imm (by decide)]
    have := hc.fit; omega
  have ep : State.addr (b + BitVec.ofNat 32 512) = State.addr b + BitVec.ofNat 64 512 :=
    addr_add (by have := hc.fit; omega)
  refine WP.seq ?_
  refine wp_mov (op2_reg _ _) fun x hx => WP.block_nil ?_
  have hcx := hcw.of_rest (hx.rest (ws := [.r8]) (by decide)) (by decide)
  refine WP.mono (scalarReduceEngine_ok hcx ((hx.other _ (by decide)).trans pw) pf
    (fun n hn => by rw [ep, Offset.add_add]; exact hcx.inR (by omega))
    (fun z hz => by
      rw [ep]
      simp only [scalarRegions, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl <;> exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)))
    fun t ⟨kt, lt, vt⟩ => ?_
  refine ⟨kr.trans ((hx.rest (by decide)).trans (kt.rest.mono (by decide))), ?_, lt, ?_, ?_⟩
  · have fu' : Frame [scalarWork b] s.mem u.mem := fu.sub fun z hz => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hz]; exact scalarWork_sub (by decide) (by decide)⟩
    have fv' : Frame [scalarWork b] u.mem v.mem := fv.sub fun z hz => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hz]; exact scalarWork_sub (by decide) (by decide)⟩
    have fw' : Frame [scalarWork b] v.mem w.mem := fw.sub fun z hz => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hz]; exact scalarWork_sub (by decide) (by decide)⟩
    have ft' : Frame [scalarWork b] w.mem t.mem := by
      rw [← hx.mem]
      exact kt.frame.sub fun z hz => ⟨_, List.mem_singleton_self _, by
        simp only [scalarRegions, List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl <;> exact scalarWork_sub (by decide) (by decide)⟩
    exact fu'.trans (fv'.trans (fw'.trans ft'))
  · rw [vt, ep, hx.mem, vw, sum, Nat.add_comm]
  · rw [kt.rest.gpr _ (by decide), hx.gpr, kw.gpr _ (by decide), kv.gpr _ (by decide), ku.gpr _ (by decide)]

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarMulAddMain`. -/
section
/-! Merged from `Proof.Ed25519.Arm.ScalarMulAddArgs`. -/
section
/-! Preserve the input pointers and callee-saved registers before arithmetic. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def ScalarArgs (b : BitVec 32) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ i < 4, m.readW (State.addr b + BitVec.ofNat 64 (32 + 4 * i)) 32 = g (scalarArgReg i)

theorem scalarStoreArgs_ok {b : BitVec 32} {s : State} (hp : s.gpr .r12 = b)
    (hfit : b.toNat + 8192 ≤ 2 ^ 32) (hw : (⟨State.addr b, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block scalarStoreArgs) s fun t => ScalarArgs b s.gpr t.mem ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 32, 16⟩] s.mem t.mem ∧ t.gpr = s.gpr ∧ Rest [] s t := by
  refine wp_range_flatMap (M := isa)
    (fun n t => (∀ i < n, t.mem.readW (State.addr b + BitVec.ofNat 64 (32 + 4 * i)) 32 =
      s.gpr (scalarArgReg i)) ∧ Frame [⟨State.addr b + BitVec.ofNat 64 32, 4 * n⟩] s.mem t.mem ∧
      t.gpr = s.gpr ∧ Rest [] s t)
    (fun n t hn ⟨hval, hf, hg, hk⟩ => ?_) 4 (Nat.le_refl _) s
    ⟨fun _ h => by omega, Frame.refl _ _, rfl, Rest.refl _ _⟩
  refine wp_str (a := State.addr b + BitVec.ofNat 64 (32 + 4 * n)) (by omega)
    (by rw [hg, hp]; exact addr_add (by omega))
    (by rw [hk.wr]; exact in_base hw (by omega) (by omega)) fun u hu => WP.block_nil ?_
  refine ⟨fun i hi => ?_, ?_, by rw [hu.gpr, hg], hk.trans (hu.rest _)⟩
  · rw [hu.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact hval i hi
    · rw [Mem.readW_writeW_self32, hg]
  · rw [hu.mem]
    exact (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))

theorem scalar_ldrSp {s : State} {is : List Instr} {Q : State → Prop}
    (hr : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (k : ∀ t, Upd s t .r12 (stackArg s 0) → WP isa (.block is) t Q) :
    WP isa (.block (.ldrSp .r12 0 :: is)) s Q := by
  refine WP.cons (s' := s.setReg .r12 (stackArg s 0)) ?_ (k _ (Upd.setReg _ _ _))
  simp only [exec, show (0 : Nat) < 4096 from by decide, ite_true, State.load32,
    BitVec.add_zero, hr, Option.map_some]
  simp [stackArg, stackArgAddr]

theorem scalarMulAddArgs_ok {s : State}
    (hr : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (hfit : (stackArg s 0).toNat + 8192 ≤ 2 ^ 32)
    (hw : (⟨State.addr (stackArg s 0), 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block scalarMulAddArgs) s fun t =>
      Ctx (stackArg s 0) t ∧ ScalarSaved (State.addr (stackArg s 0)) s.gpr t.mem ∧
      ScalarArgs (stackArg s 0) s.gpr t.mem ∧ Rest [.r0, .r12] s t ∧
      Frame [⟨State.addr (stackArg s 0), 48⟩] s.mem t.mem := by
  rw [scalarMulAddArgs, List.append_assoc, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine scalar_ldrSp hr fun u hu => ?_
  refine WP.append (scalarSave_ok hu.gpr hfit (hu.wr ▸ hw)) fun v ⟨sv, fv, gv, kv⟩ => ?_
  refine WP.append (scalarStoreArgs_ok (by rw [gv]; exact hu.gpr) hfit
    (by rw [kv.wr, hu.wr]; exact hw)) fun w ⟨aw, fw, gw, kw⟩ => ?_
  refine wp_mov (op2_reg _ _) fun t ht => WP.block_nil ?_
  have kt : Rest [.r0, .r12] s t := (hu.rest (by decide)).trans
    ((kv.mono (by decide)).trans ((kw.mono (by decide)).trans (ht.rest (by decide))))
  refine ⟨⟨?_, hfit, by rw [kt.wr]; exact hw⟩, ?_, ?_, kt, ?_⟩
  · rw [ht.gpr, gw, gv, hu.gpr]
  · have sn : ∀ i < 8, scalarSavedReg i ≠ .r12 := by decide
    intro i hi
    rw [ht.mem, fw.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), sv i hi]
    · exact hu.other _ (sn i hi)
    · rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  · have an : ∀ i < 4, scalarArgReg i ≠ .r12 := by decide
    intro i hi
    rw [ht.mem, aw i hi, gv]
    exact hu.other _ (an i hi)
  · rw [ht.mem, ← hu.mem]
    exact (fv.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).trans
      (fw.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by decide)⟩)

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarMulAddInputs`. -/
section
/-! Merged from `Proof.Ed25519.Arm.ScalarLoadInput`. -/
section
/-! Load a scalar using a saved public input pointer. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarLoadInput_ok {b p : BitVec 32} {o ptrOff : Nat} {s : State} (hc : Ctx b s)
    (ho : o + 64 ≤ 4096) (hm : ptrOff + 4 ≤ 4096)
    (hp : s.mem.readW (State.addr b + BitVec.ofNat 64 ptrOff) 32 = p)
    (hfit : p.toNat + 32 ≤ 2 ^ 32)
    (hr : (⟨State.addr p, 32⟩ : Region) ∈ s.rd ++ s.wr)
    (hsep : (⟨State.addr p, 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩) :
    WP isa (.block (scalarLoadInput o ptrOff)) s fun t =>
      Rest [.r2, .r3, .r12] s t ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s.mem t.mem ∧
      Lim t.mem (State.addr b) o ∧ V t.mem (State.addr b) o =
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr p) 32) := by
  unfold scalarLoadInput
  simp only [List.cons_append, List.nil_append]
  refine ldr0_ok hc hm fun u hu => ?_
  have hcu := hc.of_rest (hu.rest (ws := [.r12]) (by decide)) (by decide)
  refine WP.mono (unpackField_ok (p := p) (src := 0) hcu ho (by decide) (hu.gpr.trans hp) (by omega)
    (fun i hi => by rw [hu.rd, hu.wr]; simpa only [Nat.zero_add] using in_base hr (by omega) (by omega))
    (by simpa only [BitVec.add_zero] using hsep.sub_right (Offset.sub_base _ (by omega))))
    fun t ⟨kt, ft, lt, vt⟩ => ?_
  refine ⟨(hu.rest (by decide)).trans (kt.mono (by decide)), ?_, lt, ?_⟩
  · rw [← hu.mem]; exact ft
  · rw [vt, hu.mem, BitVec.add_zero, scalar_packed_decode]

end VG.Proof.Ed25519.Arm
end

/-! Prepare the three arbitrary, unreduced 256-bit scalar inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def ScalarInputs (b : BitVec 32) (m : Mem) (p : Nat → BitVec 32) (n : Nat) (t : State) : Prop :=
  ∀ i < n, Lim t.mem (State.addr b) (64 + 64 * i) ∧
    V t.mem (State.addr b) (64 + 64 * i) =
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr (p i)) 32)

structure ScalarInputsInv (b : BitVec 32) (s0 : State) (p : Nat → BitVec 32) (n : Nat) (t : State) : Prop where
  rest : Rest [.r2, .r3, .r12] s0 t
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 64, 64 * n⟩] s0.mem t.mem
  values : ScalarInputs b s0.mem p n t

theorem scalarInputsLoop_ok {b : BitVec 32} {s : State} (hc : Ctx b s)
    {p : Nat → BitVec 32}
    (hp : ∀ i < 3, s.mem.readW (State.addr b + BitVec.ofNat 64 (36 + 4 * i)) 32 = p i)
    (hfit : ∀ i < 3, (p i).toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ i < 3, (⟨State.addr (p i), 32⟩ : Region) ∈ s.rd ++ s.wr)
    (hsep : ∀ i < 3, (⟨State.addr (p i), 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩) :
    WP isa (.block ((List.range 3).flatMap fun i => scalarLoadInput (64 + 64 * i) (36 + 4 * i))) s
      (ScalarInputsInv b s p 3) := by
  refine wp_range_flatMap (M := isa) (ScalarInputsInv b s p)
    (fun n t hn ht => ?_) 3 (Nat.le_refl _) s
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => by omega⟩
  have hct := hc.of_rest ht.rest (by decide)
  have ptr : t.mem.readW (State.addr b + BitVec.ofNat 64 (36 + 4 * n)) 32 = p n := by
    rw [ht.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), hp n hn]
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  refine WP.mono (scalarLoadInput_ok hct (by omega) (by omega) ptr (hfit n hn)
    (by rw [ht.rest.rd, ht.rest.wr]; exact hr n hn) (hsep n hn)) fun u ⟨ku, fu, lu, vu⟩ => ?_
  refine ⟨ht.rest.trans ku, ?_, fun i hi => ?_⟩
  · exact (ht.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).trans
      (fu.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)⟩)
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have eq : ∀ k < 16, limb u.mem (State.addr b) (64 + 64 * i) k =
          limb t.mem (State.addr b) (64 + 64 * i) k :=
        limb_frame fu fun r hr k hk => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
      exact ⟨fun k hk => by rw [eq k hk]; exact (ht.values i hi).1 k hk,
        (val16_congr eq).trans (ht.values i hi).2⟩
    · refine ⟨lu, ?_⟩
      rw [vu]
      apply congrArg Spec.Ed25519.decodeLE
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun k hk => ht.frame.bytes
        (R := ⟨State.addr (p i), 32⟩) (fun r hr => ?_) (by decide : 32 ≤ 2 ^ 64) (List.mem_range.mp hk)
      rw [List.mem_singleton.mp hr]
      exact (hsep i hn).sub_right (Offset.sub_base _ (by omega))

theorem scalarMulAddInputs_ok {b q : BitVec 32} {s : State} (hc : Ctx b s)
    {p : Nat → BitVec 32}
    (hp : ∀ i < 3, s.mem.readW (State.addr b + BitVec.ofNat 64 (36 + 4 * i)) 32 = p i)
    (hfit : ∀ i < 3, (p i).toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ i < 3, (⟨State.addr (p i), 32⟩ : Region) ∈ s.rd ++ s.wr)
    (hsep : ∀ i < 3, (⟨State.addr (p i), 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩)
    (hout : s.mem.readW (State.addr b + BitVec.ofNat 64 32) 32 = q) :
    WP isa (.block scalarMulAddInputs) s fun t =>
      Rest [.r2, .r3, .r10, .r12] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 64, 192⟩] s.mem t.mem ∧
      ScalarInputs b s.mem p 3 t ∧ t.gpr .r10 = q := by
  unfold scalarMulAddInputs
  refine WP.append (scalarInputsLoop_ok hc hp hfit hr hsep) fun u hu => ?_
  refine ldr0_ok (hc.of_rest hu.rest (by decide)) (by decide) fun t ht => WP.block_nil ?_
  refine ⟨(hu.rest.mono (by decide)).trans (ht.rest (by decide)), by rw [ht.mem]; exact hu.frame,
    fun i hi => by rw [show t.mem = u.mem from ht.mem]; exact hu.values i hi, ?_⟩
  rw [ht.gpr, hu.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), hout]
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarMulAddFinish`. -/
section
/-! Encode the scalar using the output pointer kept public across arithmetic. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarMulAddFinish_ok {b p : BitVec 32} {s : State} (hc : Ctx b s)
    (hl : Lim s.mem (State.addr b) SR) (hp : s.gpr .r8 = p)
    (hfit : p.toNat + 32 ≤ 2 ^ 32) (hw : (⟨State.addr p, 32⟩ : Region) ∈ s.wr)
    (hsep : (⟨State.addr p, 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩)
    {g : Reg → BitVec 32} (hs : ScalarSaved (State.addr b) g s.mem) :
    WP isa (.block scalarMulAddFinish) s fun t =>
      (∀ i < 8, t.gpr (scalarSavedReg i) = g (scalarSavedReg i)) ∧ Rest scalarFinishClob s t ∧
      Frame [⟨State.addr p, 32⟩] s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr p) 32 = Spec.Ed25519.encodeLE 32 (V s.mem (State.addr b) SR) := by
  rw [scalarMulAddFinish, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun u hu => ?_
  have hcu := hc.of_rest (hu.rest (ws := [.r12]) (by decide)) (by decide)
  refine WP.append (packField_ok (p := p) (a := SR) (dst := 0) hcu (by decide) (hu.mem ▸ hl) (by decide)
    (hu.gpr.trans hp) (by omega)
    (fun i hi => by rw [hu.wr]; simpa only [Nat.zero_add] using in_base hw (by omega) (by omega))
    (by simpa only [BitVec.add_zero] using
      hsep.symm.sub_left (Offset.sub_base _ (by decide : SR + 64 ≤ 8192))))
    fun v ⟨kv, fv, vv⟩ => ?_
  have hcv := hcu.of_rest kv (by decide)
  have hs' : ScalarSaved (State.addr b) g v.mem :=
    (hu.mem ▸ hs).frame fv fun r hr i hi => by
      rw [List.mem_singleton.mp hr, BitVec.add_zero]
      exact hsep.symm.sub_left (Offset.sub_base _ (by omega))
  refine WP.mono (scalarRestore_ok hcv hs') fun t ⟨saved, kt, mt⟩ => ?_
  refine ⟨saved, (hu.rest (by decide)).trans ((kv.mono (by decide)).trans (kt.mono (by decide))), ?_, ?_⟩
  · rw [mt, ← hu.mem]; simpa only [BitVec.add_zero] using fv
  · rw [mt, scalar_packed_encode, ← hu.mem]
    have e : packedV v.mem (State.addr p) = V u.mem (State.addr b) SR := by
      simpa only [BitVec.add_zero] using vv
    exact congrArg (Spec.Ed25519.encodeLE 32) e

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarMulAddContract`. -/
section
/-! A local contract for the five-argument scalar multiply-add ABI. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def scalarMulAddLocal : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 32⟩
    let r : Region := ⟨State.addr (s.gpr .r1), 32⟩
    let k : Region := ⟨State.addr (s.gpr .r2), 32⟩
    let a : Region := ⟨State.addr (s.gpr .r3), 32⟩
    let ws : Region := ⟨State.addr (stackArg s 0), 8192⟩
    let args : Region := ⟨State.addr s.sp, 4⟩
    s.rd = [r, k, a, args] ∧ s.wr = [out, ws] ∧
      out.Disjoint ws ∧ r.Disjoint ws ∧ k.Disjoint ws ∧ a.Disjoint ws ∧
      out.Disjoint args ∧ ws.Disjoint args ∧
      (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 32 ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + 8192 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32
  post s t := Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r0)) 32 =
    Spec.Ed25519.scalarMulAdd (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32)
      (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32)
      (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r3)) 32)
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧
    s.gpr .r2 = t.gpr .r2 ∧ s.gpr .r3 = t.gpr .r3 ∧ stackArg s 0 = stackArg t 0

structure ScalarMulAddPre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r1), 32⟩, ⟨State.addr (s.gpr .r2), 32⟩,
    ⟨State.addr (s.gpr .r3), 32⟩, ⟨State.addr s.sp, 4⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r0), 32⟩, ⟨State.addr (stackArg s 0), 8192⟩]
  out_ws : (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 8192⟩
  r_ws : (⟨State.addr (s.gpr .r1), 32⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 8192⟩
  k_ws : (⟨State.addr (s.gpr .r2), 32⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 8192⟩
  a_ws : (⟨State.addr (s.gpr .r3), 32⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 8192⟩
  out_args : (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr s.sp, 4⟩
  ws_args : (⟨State.addr (stackArg s 0), 8192⟩ : Region).Disjoint ⟨State.addr s.sp, 4⟩
  f0 : (s.gpr .r0).toNat + 32 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 32 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 32 ≤ 2 ^ 32
  f3 : (s.gpr .r3).toNat + 32 ≤ 2 ^ 32
  fs : (stackArg s 0).toNat + 8192 ≤ 2 ^ 32
  fsp : s.sp.toNat + 4 ≤ 2 ^ 32

theorem ScalarMulAddPre.of {s : State} (h : scalarMulAddLocal.pre s) : ScalarMulAddPre s := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem ScalarMulAddPre.input {s : State} (h : ScalarMulAddPre s) {i : Nat} (hi : i < 3) :
    (s.gpr (scalarArgReg (i + 1))).toNat + 32 ≤ 2 ^ 32 ∧
    (⟨State.addr (s.gpr (scalarArgReg (i + 1))), 32⟩ : Region) ∈ s.rd ++ s.wr ∧
    (⟨State.addr (s.gpr (scalarArgReg (i + 1))), 32⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 8192⟩ := by
  have hc : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · exact ⟨h.f1, by rw [h.rd]; simp [scalarArgReg], h.r_ws⟩
  · exact ⟨h.f2, by rw [h.rd]; simp [scalarArgReg], h.k_ws⟩
  · exact ⟨h.f3, by rw [h.rd]; simp [scalarArgReg], h.a_ws⟩

end VG.Proof.Ed25519.Arm
end

/-! The complete scalar multiply-add function and ARM calling convention. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarMulAdd_correct {s : State} (h : ScalarMulAddPre s) :
    WP isa scalarMulAdd s fun t => abiPreserved s t ∧ scalarMulAddLocal.post s t := by
  let b := stackArg s 0
  let ptr := fun i => s.gpr (scalarArgReg (i + 1))
  have hw : (⟨State.addr b, 8192⟩ : Region) ∈ s.wr := by rw [h.wr]; simp [b]
  have ha : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4 :=
    ⟨_, by rw [h.rd]; simp, Region.contains_self _ _⟩
  unfold scalarMulAdd
  refine WP.seq (WP.append (scalarMulAddArgs_ok ha h.fs hw) fun u ⟨hcu, su, au, ku, fu⟩ => ?_)
  refine WP.mono (scalarMulAddInputs_ok (p := ptr) (q := s.gpr .r0) hcu
    (fun i hi => by
      have e := au (i + 1) (by omega)
      rw [show 32 + 4 * (i + 1) = 36 + 4 * i by omega] at e
      exact e)
    (fun i hi => (h.input hi).1)
    (fun i hi => by rw [ku.rd, ku.wr]; exact (h.input hi).2.1)
    (fun i hi => (h.input hi).2.2) (au 0 (by decide))) fun v ⟨kv, fv, iv, ov⟩ => ?_
  have hcv := hcu.of_rest kv (by decide)
  refine WP.seq (WP.mono (scalarMulAddEngine_ok hcv (iv 0 (by decide)).1
    (iv 1 (by decide)).1 (iv 2 (by decide)).1) fun w ⟨kw, fw, lw, vw, ow⟩ => ?_)
  have sw : ScalarSaved (State.addr b) s.gpr w.mem :=
    (su.frame fv fun r hr i hi => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)).frame
      fw fun r hr i hi => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  refine WP.mono (scalarMulAddFinish_ok (hcv.of_rest kw (by decide)) lw (ow.trans ov) h.f0
    (by rw [kw.wr, kv.wr, ku.wr, h.wr]; simp) h.out_ws sw) fun t ⟨gt, kt, _, bt⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [kt.sp, kw.sp, kv.sp, ku.sp]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact gt 0 (by decide)
    · exact gt 1 (by decide)
    · exact gt 2 (by decide)
    · exact gt 3 (by decide)
    · exact gt 4 (by decide)
    · exact gt 5 (by decide)
    · exact gt 6 (by decide)
    · exact gt 7 (by decide)
    · rw [kt.gpr _ (by decide), kw.gpr _ (by decide), kv.gpr _ (by decide), ku.gpr _ (by decide)]
  · have inputs : ∀ i < 3, V v.mem (State.addr b) (64 + 64 * i) =
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (ptr i)) 32) := by
      intro i hi
      rw [(iv i hi).2]
      apply congrArg Spec.Ed25519.decodeLE
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun k hk => fu.bytes (R := ⟨State.addr (ptr i), 32⟩)
        (fun r hr => ?_) (by decide : 32 ≤ 2 ^ 64) (List.mem_range.mp hk)
      rw [List.mem_singleton.mp hr]
      exact (h.input hi).2.2.sub_right (Region.sub_prefix (by decide))
    change Spec.Ed25519.bytesAt t.mem _ 32 = Spec.Ed25519.encodeLE 32 _
    rw [bt, vw, inputs 0 (by decide), inputs 1 (by decide), inputs 2 (by decide)]
    rfl

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarMulAddLit`. -/
section
namespace VG.Impl.Ed25519.Arm
materialize_code scalarMulAdd
end VG.Impl.Ed25519.Arm
end

/-! The complete multiply-add primitive satisfies the reviewed contract. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def scalarMulAddTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [32, 8192],
    argLen := 4, argBases := [(0, 1)] }

theorem scalarMulAddTaint_wf {s : State} (h : scalarMulAddLocal.pre s) :
    VG.Arm.Taint.Wf scalarMulAddTaint s := by
  have hp := ScalarMulAddPre.of h
  refine ⟨fun _ => ⟨by simp [hp.wr, scalarMulAddTaint], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hp.fsp, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact hp.out_ws
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · simpa only [State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using hp.f0
    · simpa only [State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using hp.fs
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.out_args.symm
    · exact hp.ws_args.symm
  · intro p hm
    simp only [scalarMulAddTaint, List.mem_singleton] at hm
    subst hm
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem scalarMulAdd_argByte (s : State) (k : Nat) :
    VG.Arm.Taint.argByte s k = stackArgAddr s 0 + BitVec.ofNat 64 k := by
  simp [VG.Arm.Taint.argByte, stackArgAddr]

theorem scalarMulAdd_ct : ConstantTime isa scalarMulAddLocal.pre scalarMulAddLocal.pub scalarMulAdd := by
  refine VG.Taint.constantTime (A := taint) scalarMulAddTaint ?_ (by taint_decide)
  intro s t hs ht ⟨hsp, h0, h1, h2, h3, ha⟩
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, scalarMulAddTaint_wf hs, scalarMulAddTaint_wf ht,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => hsp, fun k hk => ?_⟩
  · simp only [scalarMulAddTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [(ScalarMulAddPre.of hs).wr, (ScalarMulAddPre.of ht).wr, h0, ha]
  · rw [scalarMulAdd_argByte, scalarMulAdd_argByte, Mem.readW_byte s.mem _ hk, Mem.readW_byte t.mem _ hk]
    exact congrArg (fun v : BitVec 32 => v.extractLsb' (8 * k) 8) ha

def scalarMulAddSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x50 else 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x5000, 8192⟩]

theorem scalarMulAdd_ok (s : State) (hs : scalarMulAddLocal.pre s) :
    ∃ t s', Exec isa scalarMulAdd s t s' ∧ abiPreserved s s' ∧ scalarMulAddLocal.post s s' :=
  scalarMulAdd_correct (ScalarMulAddPre.of hs)

theorem scalarMulAdd_verified : Verified Arm.target scalarMulAdd
    (Spec.Ed25519.scalarMulAddContract Arm.abi) :=
  Verified.of_correct scalarMulAdd_ok scalarMulAdd_ct (by
    sig_implies [Spec.Ed25519.scalarMulAddContract, Spec.Ed25519.scalarMulAddSig,
      Spec.Ed25519.scratchWords, scalarMulAddLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
      [scalarMulAddSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using scalarMulAddSat)

end VG.Proof.Ed25519.Arm
