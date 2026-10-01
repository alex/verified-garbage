import VerifiedGarbage.Proof.Ed25519.Arm.ScalarPackWide
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarLoop

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
  have sum : val16 (accw v.mem (State.addr b)) 32 =
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
