import VerifiedGarbage.Proof.X25519.Arm.Invert
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# X25519 on 32-bit ARM: the final reduction and the output

`freeze` stores the 32 bytes of the element at `X2`, reduced fully modulo `p`,
at `out` (`freeze_ok`).
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P Fe bytesAt)
open VG.Proof.X25519 (leBytes)

theorem low15_val (x : BitVec 32) : ((x <<< 17) >>> 17).toNat = x.toNat % 32768 := by
  rw [toNat_shr, toNat_shl, show (2 : Nat) ^ 32 = 32768 * 2 ^ 17 from rfl, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

theorem sel0r (a c : BitVec 32) : a ^^^ ((c ^^^ a) &&& (0 - BitVec.ofNat 32 0)) = a := by simp

theorem sel1r (a c : BitVec 32) : a ^^^ ((c ^^^ a) &&& (0 - BitVec.ofNat 32 1)) = c := by
  have : (0 : BitVec 32) - BitVec.ofNat 32 1 = BitVec.allOnes 32 := by decide
  rw [this, BitVec.and_allOnes, BitVec.xor_comm c, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem byte_eq {v : BitVec 32} {n : Nat} (h : v.toNat = n) : v.setWidth 8 = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, h]

theorem ofNat8_eq {a c : Nat} (h : a % 256 = c % 256) : BitVec.ofNat 8 a = BitVec.ofNat 8 c := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; exact h

/-- The bytes at `O` are those of `X`, if the bytes `2k` and `2k + 1` are those
of limb `k`. -/
theorem bytesAt_limbs {m : Mem} {O : Addr} {r : Nat → Nat} (hr : ∀ k < 16, r k < 65536)
    (h0 : ∀ k < 16, m (O + BitVec.ofNat 64 (2 * k)) = BitVec.ofNat 8 (r k))
    (h1 : ∀ k < 16, m (O + BitVec.ofNat 64 (2 * k + 1)) = BitVec.ofNat 8 (r k / 256)) :
    bytesAt m O 32 = leBytes 32 (val16 r 16) := by
  simp only [bytesAt, leBytes]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hk : i / 2 < 16 := by omega
  obtain ⟨b0, b1⟩ := bytes_of_limbs hr hk
  rcases Nat.mod_two_eq_zero_or_one i with he | ho
  · rw [show i = 2 * (i / 2) by omega, h0 _ hk]
    exact ofNat8_eq b0.symm
  · rw [show i = 2 * (i / 2) + 1 by omega, h1 _ hk]
    refine ofNat8_eq ?_
    rw [b1, Nat.mod_eq_of_lt (by have := hr _ hk; omega)]

section
variable {b : BitVec 32}

/-- The start of `freeze`: bit 255 of `[X2]` cleared, 19 times it in `r5`. -/
theorem freezeA_ok {s : State} (hc : Ctx b s) (hl : Lim s.mem (State.addr b) X2) :
    WP isa (.block freezeA) s fun s' =>
      s'.gpr .r6 = mask16 ∧ (s'.gpr .r5).toNat = 19 * (limb s.mem (State.addr b) X2 15 / 32768) ∧
      (∀ k < 16, limb s'.mem (State.addr b) X2 k = mask15 (limb s.mem (State.addr b) X2) k) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 X2, 64⟩] s.mem s'.mem ∧
      Rest [.r2, .r3, .r5, .r6] s s' := by
  have hX : X2 = 128 := rfl
  simp only [freezeA, low15, List.cons_append, List.nil_append]
  refine wp_movw fun s1 u1 => ?_
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.r6]) (by decide)) (by decide)
  refine ldr0_ok hc1 (d := X2 + 60) (by decide) fun s2 u2 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s3 u3 => wp_mov (op2_lsl (by decide)) fun s4 u4 =>
    wp_mov (op2_lsr (by decide)) fun s5 u5 => ?_
  have hr5 : Rest [.r3, .r5, .r6] s s5 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide)))))
  have hc5 : Ctx b s5 := hc.of_rest hr5 (by decide)
  refine str0_ok hc5 (d := X2 + 60) (by decide) fun s6 u6 => ?_
  refine wp_mov (op2_imm (by decide)) fun s7 u7 => wp_mul fun s8 u8 => WP.block_nil ?_
  have hl15 := hl 15 (by decide)
  have e2 : (s2.gpr .r3).toNat = limb s.mem (State.addr b) X2 15 := by rw [u2.gpr, u1.mem]; rfl
  have e5 : (s5.gpr .r3).toNat = limb s.mem (State.addr b) X2 15 % 32768 := by
    rw [u5.gpr, u4.gpr, low15_val, u3.other .r3 (by decide), e2]
  have e3 : (s3.gpr .r5).toNat = limb s.mem (State.addr b) X2 15 / 32768 := by
    rw [u3.gpr, toNat_shr, e2]
  have hm6 : s6.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (X2 + 60)) (s5.gpr .r3) := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨?_, ?_, fun k hk => ?_, ?_, ?_⟩
  · rw [u8.other _ (by decide), u7.other _ (by decide), u6.gpr, u5.other .r6 (by decide),
      u4.other .r6 (by decide), u3.other .r6 (by decide), u2.other .r6 (by decide), u1.gpr]
  · rw [u8.gpr, u7.other _ (by decide), u7.gpr, u6.gpr, u5.other _ (by decide), u4.other _ (by decide),
      toNat_mul_lt (by rw [e3]; show _ * 19 < _; omega), e3]
    show _ * 19 = _
    omega
  · rw [limb, u8.mem, u7.mem, hm6]
    rcases Nat.lt_or_ge k 15 with h | h
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      simp only [mask15, show k ≠ 15 by omega, ite_false]; rfl
    · rw [show X2 + 4 * k = X2 + 60 by omega, wd_write_self, e5, show k = 15 by omega]; rfl
  · rw [u8.mem, u7.mem, hm6]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (d := X2 + 60) (n := 4) (Nat.le_add_right _ _) (by omega) (by omega))
  · exact (hr5.mono (by decide)).trans ((u6.rest _).trans ((u7.rest (by decide)).trans (u8.rest (by decide))))

/-- `freezeB`: the mask `-(bit 255 of [Y])` in `r9`, and bit 255 of `[Y]` cleared. -/
theorem freezeB_ok {s : State} (hc : Ctx b s) :
    WP isa (.block freezeB) s fun s' =>
      s'.gpr .r9 = 0 - BitVec.ofNat 32 (limb s.mem (State.addr b) Y 15 / 32768) ∧
      (∀ k < 16, limb s'.mem (State.addr b) Y k = mask15 (limb s.mem (State.addr b) Y) k) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 Y, 64⟩] s.mem s'.mem ∧ Rest [.r1, .r3, .r9] s s' := by
  have hY : Y = 1088 := rfl
  simp only [freezeB, low15, List.cons_append, List.nil_append]
  refine ldr0_ok hc (d := Y + 60) (by decide) fun s1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => wp_mov (op2_imm (by decide)) fun s3 u3 =>
    wp_dp (op2_reg _ _) fun s4 u4 => wp_mov (op2_lsl (by decide)) fun s5 u5 =>
    wp_mov (op2_lsr (by decide)) fun s6 u6 => ?_
  have hr6 : Rest [.r1, .r3, .r9] s s6 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  refine str0_ok (hc.of_rest hr6 (by decide)) (d := Y + 60) (by decide) fun s7 u7 => WP.block_nil ?_
  have e1 : (s1.gpr .r3).toNat = limb s.mem (State.addr b) Y 15 := by rw [u1.gpr]; rfl
  have hm7 : s7.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (Y + 60)) (s6.gpr .r3) := by
    rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨?_, fun k hk => ?_, ?_, hr6.trans (u7.rest _)⟩
  · rw [u7.gpr, u6.other _ (by decide), u5.other _ (by decide), u4.gpr]
    show s3.gpr .r1 - s3.gpr .r9 = _
    rw [u3.gpr, u3.other _ (by decide), u2.gpr]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [toNat_shr, e1, toNat_imm (by have := wd_lt s.mem (State.addr b) (Y + 4 * 15); unfold limb; omega)]
  · rw [limb, hm7]
    rcases Nat.lt_or_ge k 15 with h | h
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      simp only [mask15, show k ≠ 15 by omega, ite_false]; rfl
    · rw [show Y + 4 * k = Y + 60 by omega, wd_write_self, u6.gpr, u5.gpr, low15_val, u4.other .r3 (by decide),
        u3.other .r3 (by decide), u2.other .r3 (by decide), e1, show k = 15 by omega]; rfl
  · rw [hm7]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (d := Y + 60) (n := 4) (Nat.le_add_right _ _) (by omega) (by omega))

/-- The output of `freeze` from `s0`, after `j` limbs. -/
structure OutInv (O : Addr) (r : Nat → Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  rest : Rest [.r2, .r3] s0 s
  frame : Frame [⟨O, 2 * j⟩] s0.mem s.mem
  b0 : ∀ i < j, s.mem (O + BitVec.ofNat 64 (2 * i)) = BitVec.ofNat 8 (r i)
  b1 : ∀ i < j, s.mem (O + BitVec.ofNat 64 (2 * i + 1)) = BitVec.ofNat 8 (r i / 256)

theorem out_ok {s0 : State} (hc : Ctx b s0) {o : BitVec 32} (h12 : s0.gpr .r12 = o)
    (hout : (⟨State.addr o, 32⟩ : Region) ∈ s0.wr) (hofit : o.toNat + 32 ≤ 2 ^ 32)
    (hdisj : Region.Disjoint ⟨State.addr b, 4096⟩ ⟨State.addr o, 32⟩) {sw : Nat} (hsw : sw ≤ 1)
    (h9 : s0.gpr .r9 = 0 - BitVec.ofNat 32 sw) :
    WP isa (.block ((List.range 16).flatMap outStep)) s0
      (OutInv (State.addr o) (fun k => sel sw (limb s0.mem (State.addr b) X2 k)
        (limb s0.mem (State.addr b) Y k)) s0 16) := by
  have hX : X2 = 128 := rfl
  have hY : Y = 1088 := rfl
  refine wp_range_flatMap (M := isa) _ (fun k s hk h => ?_) 16 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hcs : Ctx b s := hc.of_rest h.rest (by decide)
  -- The words of the working space are as in `s0`.
  have hw : ∀ d, d + 4 ≤ 4096 → wd s.mem (State.addr b) d = wd s0.mem (State.addr b) d := fun d hd =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hdisj.sub_left (Offset.sub_base _ hd)).sub_right (Region.sub_prefix (by omega))
  unfold outStep
  refine ldr0_ok hcs (d := X2 + 4 * k) (by omega) fun t1 v1 => ?_
  refine ldr0_ok (hcs.of_rest (v1.rest (ws := [.r2]) (by decide)) (by decide)) (d := Y + 4 * k) (by omega)
    fun t2 v2 => ?_
  refine wp_dp (op2_reg _ _) fun t3 v3 => wp_dp (op2_reg _ _) fun t4 v4 =>
    wp_dp (op2_reg _ _) fun t5 v5 => ?_
  have hr5 : Rest [.r2, .r3] s t5 :=
    (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans (v5.rest (by decide)))))
  have e12 : t5.gpr .r12 = o := by rw [hr5.gpr _ (by decide), h.rest.gpr _ (by decide), h12]
  have hwr : t5.wr = s0.wr := by rw [hr5.wr, h.rest.wr]
  refine wp_strb (a := State.addr o + BitVec.ofNat 64 (2 * k)) (by omega)
    (by rw [e12]; exact addr_add (by omega)) (by rw [hwr]; exact in_base hout (by omega) (by omega))
    fun t6 v6 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t7 v7 => ?_
  refine wp_strb (a := State.addr o + BitVec.ofNat 64 (2 * k + 1)) (by omega)
    (by rw [v7.other _ (by decide), v6.gpr, e12]; exact addr_add (by omega))
    (by rw [v7.wr, v6.wr, hwr]; exact in_base hout (by omega) (by omega)) fun t8 v8 => WP.block_nil ?_
  -- The limb selected.
  have ev : (t5.gpr .r2).toNat = sel sw (limb s0.mem (State.addr b) X2 k) (limb s0.mem (State.addr b) Y k) := by
    have ex : t2.gpr .r2 = s.mem.readW (State.addr b + BitVec.ofNat 64 (X2 + 4 * k)) 32 := by
      rw [v2.other _ (by decide), v1.gpr]
    have ey : t2.gpr .r3 = s.mem.readW (State.addr b + BitVec.ofNat 64 (Y + 4 * k)) 32 := by
      rw [v2.gpr, v1.mem]
    have em : t3.gpr .r9 = 0 - BitVec.ofNat 32 sw := by
      rw [v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide), h.rest.gpr _ (by decide), h9]
    rw [v5.gpr]
    show (t4.gpr .r2 ^^^ t4.gpr .r3).toNat = _
    rw [v4.other .r2 (by decide), v4.gpr]
    show (t3.gpr .r2 ^^^ (t3.gpr .r3 &&& t3.gpr .r9)).toNat = _
    rw [v3.other .r2 (by decide), v3.gpr, em]
    show (t2.gpr .r2 ^^^ ((t2.gpr .r3 ^^^ t2.gpr .r2) &&& _)).toNat = _
    rw [ex, ey]
    have hx := hw (X2 + 4 * k) (by omega)
    have hy := hw (Y + 4 * k) (by omega)
    unfold wd at hx hy
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · rw [sel0r, hx]; rfl
    · rw [sel1r, hy]; rfl
  have hm8 : t8.mem = (s.mem.writeW (State.addr o + BitVec.ofNat 64 (2 * k)) ((t5.gpr .r2).setWidth 8)).writeW
      (State.addr o + BitVec.ofNat 64 (2 * k + 1)) ((t5.gpr .r2 >>> 8).setWidth 8) := by
    rw [v8.mem, v7.gpr, v7.mem, v6.gpr, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  have ne : ∀ a c : Nat, a < 32 → c < 32 → a ≠ c →
      State.addr o + BitVec.ofNat 64 a ≠ State.addr o + BitVec.ofNat 64 c :=
    fun a c ha hc' hac => Offset.add_ofNat_ne _ (by omega) (by omega) hac
  refine ⟨h.rest.trans (hr5.trans ((v6.rest _).trans ((v7.rest (by decide)).trans (v8.rest _)))), ?_,
    fun i hi => ?_, fun i hi => ?_⟩
  · rw [hm8]
    refine ((h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [hm8, VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply,
      iteF (ne _ _ (by omega) (by omega) (by omega))]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [iteF (ne _ _ (by omega) (by omega) (by omega))]; exact h.b0 i hi
    · rw [iteT rfl]; exact byte_eq ev
  · rw [hm8, VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [iteF (ne _ _ (by omega) (by omega) (by omega)), iteF (ne _ _ (by omega) (by omega) (by omega))]
      exact h.b1 i hi
    · rw [iteT rfl]
      exact byte_eq (by rw [toNat_shr, ev])

theorem frame_sub1 {m m' : Mem} {r r' : Region} {rs : List Region} (h : Frame [r] m m') (hs : Region.Sub r r')
    (hr : r' ∈ rs) : Frame rs m m' :=
  h.sub fun x hx => ⟨r', hr, by rw [List.mem_singleton.mp hx]; exact hs⟩

theorem freeze_ok {s : State} (hc : Ctx b s) (hl : Lim s.mem (State.addr b) X2) {o : BitVec 32}
    (h12 : s.gpr .r12 = o) (hout : (⟨State.addr o, 32⟩ : Region) ∈ s.wr) (hofit : o.toNat + 32 ≤ 2 ^ 32)
    (hdisj : Region.Disjoint ⟨State.addr b, 4096⟩ ⟨State.addr o, 32⟩) :
    WP isa (.block freeze) s fun s' =>
      bytesAt s'.mem (State.addr o) 32 = leBytes 32 (V s.mem (State.addr b) X2 % P) ∧ Rest clob s s' ∧
      Frame [FA b, ⟨State.addr o, 32⟩] s.mem s'.mem := by
  have hX : X2 = 128 := rfl
  have hY : Y = 1088 := rfl
  obtain ⟨tA, tY, hS, hR, hv⟩ := freeze_facts hl
  obtain ⟨-, -, lm, c1⟩ := mask15_facts hl
  simp only [freeze, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (freezeA_ok hc hl) fun s1 ⟨h6, h5, hl1, hf1, hr1⟩ => ?_
  have hc1 : Ctx b s1 := hc.of_rest hr1 (by decide)
  refine WP.append (pass_ok (rb := .r0) (o := X2) (s0 := s1) (c := mask15 (limb s.mem (State.addr b) X2))
    (cin := 19 * (limb s.mem (State.addr b) X2 15 / 32768)) (by decide) (by decide)
    (by rw [hc1.r0]; have := hc.fit; omega) (fun k hk => by rw [hc1.r0]; exact hc1.inW (by omega)) h6 h5
    (fun k hk => by have := lm k hk; omega) (by omega) ?_) fun s2 hp2 => ?_
  · intro k hk s' hp
    refine WP.mono (ldSrc_ok (hc1.of_rest hp.rest (by decide)) (o := X2) (k := k) (by omega)) fun t ht => ⟨?_, ht.2.1.mono (by decide), ht.2.2⟩
    rw [ht.1, wd_pass hc1 hp.frame (by omega) (by omega) (by omega)]
    exact hl1 k hk
  have hc2 : Ctx b s2 := hc1.of_rest hp2.rest (by decide)
  have hpo2 : ∀ j < 16, wd s2.mem (State.addr b) (X2 + 4 * j) = frA (limb s.mem (State.addr b) X2) j :=
    fun j hj => by have := hp2.outs j hj; rwa [hc1.r0] at this
  have hpf2 : Frame [⟨State.addr b + BitVec.ofNat 64 X2, 64⟩] s1.mem s2.mem := by
    have := hp2.frame; rwa [hc1.r0] at this
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  have hc3 : Ctx b s3 := hc2.of_rest (u3.rest (ws := [.r5]) (by decide)) (by decide)
  refine WP.append (pass_ok (rb := .r0) (o := Y) (s0 := s3) (c := frA (limb s.mem (State.addr b) X2))
    (cin := 19) (by decide) (by decide)
    (by rw [hc3.r0]; have := hc.fit; omega) (fun k hk => by rw [hc3.r0]; exact hc3.inW (by omega))
    (by rw [u3.other _ (by decide), hp2.rest.gpr _ (by decide)]; exact h6)
    (by rw [u3.gpr]; rfl) (fun k hk => by have := out_lt (mask15 (limb s.mem (State.addr b) X2)) (19 * (limb s.mem (State.addr b) X2 15 / 32768)) k; unfold frA; omega) (by decide) ?_) fun s4 hp4 => ?_
  · intro k hk s' hp
    refine WP.mono (ldSrc_ok (hc3.of_rest hp.rest (by decide)) (o := X2) (k := k) (by omega)) fun t ht => ⟨?_, ht.2.1.mono (by decide), ht.2.2⟩
    rw [ht.1, wd_pass hc3 hp.frame (by omega) (by omega) (by omega), u3.mem]
    exact hpo2 k hk
  have hc4 : Ctx b s4 := hc3.of_rest hp4.rest (by decide)
  have hpo4 : ∀ j < 16, wd s4.mem (State.addr b) (Y + 4 * j) = frY (limb s.mem (State.addr b) X2) j :=
    fun j hj => by have := hp4.outs j hj; rwa [hc3.r0] at this
  have hpf4 : Frame [⟨State.addr b + BitVec.ofNat 64 Y, 64⟩] s3.mem s4.mem := by
    have := hp4.frame; rwa [hc3.r0] at this
  have hx4 : ∀ k < 16, limb s4.mem (State.addr b) X2 k = frA (limb s.mem (State.addr b) X2) k := by
    intro k hk
    rw [limb, wd_frame hpf4 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega),
      u3.mem, hpo2 k hk]
  refine WP.append (freezeB_ok hc4) fun s5 ⟨h9, hy5, hf5, hr5⟩ => ?_
  have hc5 : Ctx b s5 := hc4.of_rest hr5 (by decide)
  have hx5 : ∀ k < 16, limb s5.mem (State.addr b) X2 k = frA (limb s.mem (State.addr b) X2) k := by
    intro k hk
    rw [limb, wd_frame hf5 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)]
    exact hx4 k hk
  have hy5' : ∀ k < 16, limb s5.mem (State.addr b) Y k = mask15 (frY (limb s.mem (State.addr b) X2)) k := by
    intro k hk
    rw [hy5 k hk]
    simp only [mask15]
    split
    · rename_i h; subst h; rw [limb, hpo4 15 (by decide)]
    · rw [limb, hpo4 k hk]
  have h9' : s5.gpr .r9 = 0 - BitVec.ofNat 32 (frS (limb s.mem (State.addr b) X2)) := by
    rw [h9, limb, hpo4 15 (by decide)]; rfl
  have hr45 : Rest [.r1, .r2, .r3, .r4, .r5, .r6, .r9] s s5 :=
    (hr1.mono (by decide)).trans ((hp2.rest.mono (by decide)).trans ((u3.rest (by decide)).trans
      ((hp4.rest.mono (by decide)).trans (hr5.mono (by decide)))))
  refine WP.mono (out_ok hc5 (o := o) (by rw [hr45.gpr _ (by decide), h12]) (by rw [hr45.wr]; exact hout) hofit
    hdisj hS h9') fun s6 h6' => ⟨?_, ?_, ?_⟩
  · have hr : ∀ k < 16, sel (frS (limb s.mem (State.addr b) X2)) (limb s5.mem (State.addr b) X2 k)
        (limb s5.mem (State.addr b) Y k) = frR (limb s.mem (State.addr b) X2) k := fun k hk => by
      rw [hx5 k hk, hy5' k hk]; rfl
    rw [V, ← hv]
    exact bytesAt_limbs hR (fun k hk => by rw [h6'.b0 k hk, hr k hk]) (fun k hk => by rw [h6'.b1 k hk, hr k hk])
  · exact (hr45.mono (by decide)).trans (h6'.rest.mono (by decide))
  · have hfa : ∀ z, z + 64 ≤ 1280 → 64 ≤ z → Region.Sub ⟨State.addr b + BitVec.ofNat 64 z, 64⟩ (FA b) :=
      fun z h1 h2 => Offset.sub _ (by omega) (by omega)
    refine (frame_sub1 hf1 (hfa X2 (by omega) (by omega)) (List.mem_cons_self ..)).trans ?_
    refine (frame_sub1 hpf2 (hfa X2 (by omega) (by omega)) (List.mem_cons_self ..)).trans ?_
    rw [← u3.mem]
    refine (frame_sub1 hpf4 (hfa Y (by omega) (by omega)) (List.mem_cons_self ..)).trans ?_
    refine (frame_sub1 hf5 (hfa Y (by omega) (by omega)) (List.mem_cons_self ..)).trans ?_
    exact frame_sub1 h6'.frame (Region.sub_prefix (by omega)) (List.mem_cons_of_mem _ (List.mem_singleton_self _))

end

end VG.Proof.X25519.Arm
