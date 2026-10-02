import VerifiedGarbage.Proof.X25519.Arm.Field

/-!
# X25519 on 32-bit ARM: sums and differences

`add o x y` and `sub o x y` store at `o` a number congruent to `[x] + [y]` and
`[x] - [y]` (as `[x] + 4p - [y]`), with limbs below `2¹⁶`; `o` may be `x` or
`y`.
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P)

section
variable {e : Nat} {b : BitVec 32}

/-- A word the pass has not written yet (the pass writes `[o, o + 4k)`). -/
theorem wd_pass {s0 s : State} (hc : CtxN e b s0) {o k d : Nat}
    (hf : Frame [⟨State.addr (s0.gpr .r0) + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem)
    (hd : d + 4 ≤ o ∨ o + 4 * k ≤ d) (hd' : d + 4 ≤ 4096) (ho : o + 4 * k ≤ 4096) :
    wd s.mem (State.addr b) d = wd s0.mem (State.addr b) d := by
  rw [hc.r0] at hf
  exact wd_frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ hd (by omega) (by omega)

theorem subK : ∀ k < 16, encodable (subHi k) = true ∧ encodable (subLo k) = true ∧
    (subLo k).toNat ≤ (subHi k).toNat ∧ (subHi k).toNat - (subLo k).toNat = fourP k ∧
    (subHi k).toNat ≤ 262144 := by decide

/-- A `pass` of sums, then the `tail`, with the mask in `r6`, 38 in `r8` and no
carry in `r5`. -/
theorem passTail'_ok {o : Nat} (ho : o + 64 ≤ 4096) {src : Nat → List Instr} {c : Nat → Nat}
    (hc : ∀ k < 16, c k + 65536 ≤ 2 ^ 32) (hv : val16 c 16 < 39 * 2 ^ 256) {s1 : State}
    (hc1 : CtxN e b s1) (h6 : s1.gpr .r6 = mask16) (h8 : s1.gpr .r8 = 38) (h5 : s1.gpr .r5 = 0)
    (hsrc : ∀ k < 16, ∀ s', PassInv .r0 o s1 c 0 k s' → WP isa (.block (src k)) s' fun s'' =>
        (s''.gpr .r3).toNat = c k ∧ Rest [.r2, .r3, .r4] s' s'' ∧ s''.mem = s'.mem) :
    WP isa (.block (pass .r0 o src ++ tail o)) s1 fun s' =>
      Rest [.r2, .r3, .r4, .r5] s1 s' ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s1.mem s'.mem ∧
      Lim s'.mem (State.addr b) o ∧ V s'.mem (State.addr b) o % P = val16 c 16 % P := by
  refine WP.append (pass_ok (s0 := s1) (c := c) (cin := 0) (by decide) ho
    (by rw [hc1.r0]; have := hc1.fit; omega) (fun k hk => by rw [hc1.r0]; exact hc1.inW (by omega))
    h6 (by rw [h5]; rfl) hc (by decide) hsrc) fun s2 hp => ?_
  have hc2 : CtxN e b s2 := hc1.of_rest hp.rest (by decide)
  have hpo : ∀ j < 16, wd s2.mem (State.addr b) (o + 4 * j) = out c 0 j := fun j hj => by
    have := hp.outs j hj; rwa [hc1.r0] at this
  have hpf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s1.mem s2.mem := by
    have := hp.frame; rwa [hc1.r0] at this
  have hcl := carry_le hv
  have hl2 : Lim s2.mem (State.addr b) o := fun k hk => by rw [limb, hpo k hk]; exact out_lt _ _ _
  refine WP.mono (tail_ok ho hc2 (by rw [hp.rest.gpr _ (by decide), h6])
    (by rw [hp.rest.gpr _ (by decide), h8]) hp.r5 hcl hl2) fun s3 ⟨hr3, hf3, hl3, hv3⟩ => ?_
  refine ⟨hp.rest.trans hr3, hpf.trans hf3, hl3, ?_⟩
  rw [hv3, V, val16_congr (f := limb s2.mem (State.addr b) o) (g := out c 0) (fun k hk => hpo k hk),
    chain_val, Nat.add_zero]

/-- The operations built from a `pass` of sums and the `tail`. -/
theorem passTail_ok {o : Nat} (ho : o + 64 ≤ 4096) {src : Nat → List Instr} {c : Nat → Nat}
    (hc : ∀ k < 16, c k + 65536 ≤ 2 ^ 32) (hv : val16 c 16 < 39 * 2 ^ 256) {s : State}
    (hctx : CtxN e b s)
    (hsrc : ∀ s1 : State, CtxN e b s1 → Rest clob s s1 → s1.mem = s.mem → ∀ k < 16, ∀ s',
      PassInv .r0 o s1 c 0 k s' → WP isa (.block (src k)) s' fun s'' =>
        (s''.gpr .r3).toNat = c k ∧ Rest [.r2, .r3, .r4] s' s'' ∧ s''.mem = s'.mem) :
    WP isa (.block (prologue ++ pass .r0 o src ++ tail o)) s fun s' =>
      Rest clob s s' ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s.mem s'.mem ∧
      Lim s'.mem (State.addr b) o ∧ V s'.mem (State.addr b) o % P = val16 c 16 % P := by
  rw [List.append_assoc]
  refine WP.append prologue_ok fun s1 ⟨h6, h8, h5, hr1, hm1⟩ => ?_
  have hc1 : CtxN e b s1 := hctx.of_rest hr1 (by decide)
  refine WP.mono (passTail'_ok ho hc hv hc1 h6 h8 h5 (hsrc s1 hc1 (hr1.mono (by decide)) hm1))
    fun s3 ⟨hr3, hf3, hl3, hv3⟩ => ⟨(hr1.mono (by decide)).trans (hr3.mono (by decide)),
      by rw [← hm1]; exact hf3, hl3, hv3⟩

theorem add_ok {o x y : Nat} (ho : o + 64 ≤ 4096) (hx : x + 64 ≤ 4096) (hy : y + 64 ≤ 4096)
    (hox : o = x ∨ o + 64 ≤ x ∨ x + 64 ≤ o) (hoy : o = y ∨ o + 64 ≤ y ∨ y + 64 ≤ o)
    {s : State} (hc : CtxN e b s) (hlx : Lim s.mem (State.addr b) x) (hly : Lim s.mem (State.addr b) y) :
    WP isa (.block (add o x y)) s fun s' =>
      Rest clob s s' ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s.mem s'.mem ∧
      Lim s'.mem (State.addr b) o ∧
      V s'.mem (State.addr b) o % P = (V s.mem (State.addr b) x + V s.mem (State.addr b) y) % P := by
  have hvx := V_lt hlx
  have hvy := V_lt hly
  refine WP.mono (passTail_ok (c := fun k => limb s.mem (State.addr b) x k + limb s.mem (State.addr b) y k)
    ho (fun k hk => by have := hlx k hk; have := hly k hk; omega)
    (by rw [val16_add]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add hvx hvy) (by omega)) hc ?_)
    fun s' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, by rw [h4, val16_add]; rfl⟩
  intro s1 hc1 _ hm1 k hk s' hp
  have hc' : CtxN e b s' := hc1.of_rest hp.rest (by decide)
  refine ldr0_ok hc' (d := x + 4 * k) (by omega) fun t1 v1 => ?_
  have hc1' : CtxN e b t1 := hc'.of_rest (v1.rest (ws := [.r3]) (by decide)) (by decide)
  refine ldr0_ok hc1' (d := y + 4 * k) (by omega) fun t2 v2 => ?_
  refine wp_dp (op2_reg _ _) fun t3 v3 => WP.block_nil ⟨?_, ?_, by rw [v3.mem, v2.mem, v1.mem]⟩
  · have ex : wd s'.mem (State.addr b) (x + 4 * k) = limb s.mem (State.addr b) x k := by
      rw [wd_pass hc1 hp.frame (by omega) (by omega) (by omega), hm1]; rfl
    have ey : wd t1.mem (State.addr b) (y + 4 * k) = limb s.mem (State.addr b) y k := by
      rw [v1.mem, wd_pass hc1 hp.frame (by omega) (by omega) (by omega), hm1]; rfl
    have := hlx k hk; have := hly k hk
    rw [v3.gpr]
    show (t2.gpr .r3 + t2.gpr .r2).toNat = _
    rw [v2.other .r3 (by decide), v1.gpr, v2.gpr]
    unfold wd at ex ey
    rw [toNat_add_lt (by rw [ex, ey]; omega), ex, ey]
  · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans (v3.rest (by decide)))

theorem sub_ok {o x y : Nat} (ho : o + 64 ≤ 4096) (hx : x + 64 ≤ 4096) (hy : y + 64 ≤ 4096)
    (hox : o = x ∨ o + 64 ≤ x ∨ x + 64 ≤ o) (hoy : o = y ∨ o + 64 ≤ y ∨ y + 64 ≤ o)
    {s : State} (hc : CtxN e b s) (hlx : Lim s.mem (State.addr b) x) (hly : Lim s.mem (State.addr b) y) :
    WP isa (.block (sub o x y)) s fun s' =>
      Rest clob s s' ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s.mem s'.mem ∧
      Lim s'.mem (State.addr b) o ∧
      (V s'.mem (State.addr b) o + V s.mem (State.addr b) y) % P = V s.mem (State.addr b) x % P := by
  have hvx := V_lt hlx
  have hvy := V_lt hly
  obtain ⟨hcb, hcv⟩ := subC_facts hlx hly
  have hPv : 4 * P < 2 * 2 ^ 256 := by decide
  change val16 _ 16 + V s.mem (State.addr b) y = V s.mem (State.addr b) x + 4 * P at hcv
  refine WP.mono (passTail_ok (c := subC (limb s.mem (State.addr b) x) (limb s.mem (State.addr b) y))
    ho hcb (by omega) hc ?_) fun s' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, by
      rw [Nat.add_mod, h4, ← Nat.add_mod, hcv, Nat.mul_comm, Nat.add_mul_mod_self_left]⟩
  intro s1 hc1 _ hm1 k hk s' hp
  have hc' : CtxN e b s' := hc1.of_rest hp.rest (by decide)
  obtain ⟨e1, e2, e3, e4, e5⟩ := subK k hk
  have ex : wd s'.mem (State.addr b) (x + 4 * k) = limb s.mem (State.addr b) x k := by
    rw [wd_pass hc1 hp.frame (by omega) (by omega) (by omega), hm1]; rfl
  have hX := hlx k hk
  have hY := hly k hk
  have hK := fourP_ge k hk
  refine ldr0_ok hc' (d := x + 4 * k) (by omega) fun t1 v1 => ?_
  refine wp_dp (op2_imm e1) fun t2 v2 => wp_dp (op2_imm e2) fun t3 v3 => ?_
  have hc3 : CtxN e b t3 :=
    hc'.of_rest ((v1.rest (ws := [.r3]) (by decide)).trans ((v2.rest (by decide)).trans
      (v3.rest (by decide)))) (by decide)
  refine ldr0_ok hc3 (d := y + 4 * k) (by omega) fun t4 v4 => ?_
  refine wp_dp (op2_reg _ _) fun t5 v5 => WP.block_nil ⟨?_, ?_, by
    rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]⟩
  · have ey : wd t3.mem (State.addr b) (y + 4 * k) = limb s.mem (State.addr b) y k := by
      rw [v3.mem, v2.mem, v1.mem, wd_pass hc1 hp.frame (by omega) (by omega) (by omega), hm1]; rfl
    unfold wd at ex ey
    have r1 : (t1.gpr .r3).toNat = limb s.mem (State.addr b) x k := by rw [v1.gpr, ex]
    have r2 : (t2.gpr .r3).toNat = limb s.mem (State.addr b) x k + (subHi k).toNat := by
      rw [v2.gpr]; show (t1.gpr .r3 + subHi k).toNat = _
      rw [toNat_add_lt (by rw [r1]; omega), r1]
    have r3 : (t3.gpr .r3).toNat = limb s.mem (State.addr b) x k + fourP k := by
      rw [v3.gpr]; show (t2.gpr .r3 - subLo k).toNat = _
      rw [toNat_sub_le (by rw [r2]; omega), r2]; omega
    rw [v5.gpr]
    show (t4.gpr .r3 - t4.gpr .r2).toNat = _
    rw [v4.other .r3 (by decide), v4.gpr, toNat_sub_le (by rw [r3, ey]; omega), r3, ey]; rfl
  · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans (v5.rest (by decide)))))

end

end VG.Proof.X25519.Arm
