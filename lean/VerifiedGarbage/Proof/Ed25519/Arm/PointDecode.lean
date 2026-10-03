import VerifiedGarbage.Impl.Ed25519.Arm.PointDecode
import VerifiedGarbage.Proof.Ed25519.Arm.DecodeKeep
import VerifiedGarbage.Impl.Ed25519.Arm.FieldCheck
import VerifiedGarbage.Proof.Ed25519.Arm.Field
import VerifiedGarbage.Proof.Ed25519.Arm.Freeze
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Decode

/-! Merged from `Proof.Ed25519.Arm.SplitYSign`. -/
section
/-! Separate bit 255 while retaining all bounded field limbs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem bitNat_eq {q : Nat} (hq : q ≤ 1) : (q == 1).toNat = q := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with rfl | rfl <;> rfl

theorem splitYSign_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base) :
    WP isa (.block splitYSign) s fun t => DecodeKeep base s t ∧ AllLim t.mem base ∧
      V t.mem (State.addr base) (offset 1) = V s.mem (State.addr base) (offset 1) % 2 ^ 255 ∧
      t.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 =
        BitVec.ofNat 32 (V s.mem (State.addr base) (offset 1) / 2 ^ 255 == 1).toNat := by
  let f := limb s.mem (State.addr base) (offset 1)
  have hoff : offset (1 : Slot) = 128 := rfl
  have mf := mask15_facts (hl 1)
  refine ldr0_ok hc (by decide) fun s1 u1 => wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  have r2 : Rest [.r2, .r3, .r4] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have e2 : (s2.gpr .r2).toNat = f 15 / 32768 := by rw [u2.gpr, toNat_shr, u1.gpr]; rfl
  refine str0_ok (hc.of_rest r2 (by decide)) (by decide) fun s3 u3 => ?_
  have m3 : s3.mem = s.mem.writeW (State.addr base + BitVec.ofNat 64 60) (s2.gpr .r2) := by
    rw [u3.mem, u2.mem, u1.mem]
  have f3 : Frame [⟨State.addr base + BitVec.ofNat 64 60, 4⟩] s.mem s3.mem := by
    rw [m3]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have r3 : Rest [.r2, .r3, .r4] s s3 := r2.trans (u3.rest _)
  refine wp_movw fun s4 u4 => wp_dp (op2_reg _ _) fun s5 u5 => ?_
  have r5 : Rest [.r2, .r3, .r4] s s5 := r3.trans ((u4.rest (by decide)).trans (u5.rest (by decide)))
  have e5 : (s5.gpr .r3).toNat = f 15 % 32768 := by
    rw [u5.gpr]
    change (s4.gpr .r3 &&& s4.gpr .r4).toNat = _
    rw [BitVec.toNat_and, u4.gpr, u4.other _ (by decide), u3.gpr, u2.other _ (by decide), u1.gpr]
    change f 15 &&& (2 ^ 15 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
  refine str0_ok (hc.of_rest r5 (by decide)) (by decide) fun t ht => WP.block_nil ?_
  have mt : t.mem = s3.mem.writeW (State.addr base + BitVec.ofNat 64 (offset 1 + 60)) (s5.gpr .r3) := by
    rw [ht.mem, u5.mem, u4.mem]
  have ft : Frame [⟨State.addr base + BitVec.ofNat 64 (offset 1), 64⟩] s3.mem t.mem := by
    rw [mt]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (State.addr base) (d := offset 1 + 60) (n := 4) (e := offset 1) (k := 64)
        (by decide) (by decide) (by decide))
  have ys : ∀ k < 16, limb s3.mem (State.addr base) (offset 1) k = f k :=
    limb_frame f3 fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by decide)
  have yt : ∀ k < 16, limb t.mem (State.addr base) (offset 1) k = mask15 f k := by
    intro k hk
    rw [limb, mt]
    by_cases hk15 : k = 15
    · subst hk15
      rw [wd_write_self, e5]
      rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      change limb s3.mem (State.addr base) (offset 1) k = _
      rw [ys k hk]
      simp only [mask15, hk15, ite_false]
  have lt : AllLim t.mem base := (field_update 1 (smallFrame_lim f3 (by decide) hl) (frame_o ft)
    (fun k hk => by rw [yt k hk]; exact mf.2.2.1 k hk)).1
  refine ⟨⟨(r5.trans (ht.rest _)).mono (by decide), ?_⟩, lt, ?_, ?_⟩
  · exact (f3.mono (fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..)).trans
      (ft.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by
        rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩)
  · rw [V, val16_congr yt]
    have hv : V s.mem (State.addr base) (offset 1) = val16 (mask15 f) 16 + 2 ^ 255 * (f 15 / 32768) := mf.1
    have hb : val16 (mask15 f) 16 < 2 ^ 255 := mf.2.1
    omega
  · apply BitVec.eq_of_toNat_eq
    have hz : wd t.mem (State.addr base) 60 = (s2.gpr .r2).toNat := by
      rw [wd_frame ft (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)),
        wd, m3, Mem.readW_writeW_self32]
    change wd t.mem (State.addr base) 60 = _
    rw [hz, e2, toNat_imm (by have := Bool.toNat_le (V s.mem (State.addr base) (offset 1) / 2 ^ 255 == 1); omega)]
    have he : V s.mem (State.addr base) (offset 1) / 2 ^ 255 = f 15 / 32768 := by
      have hv : V s.mem (State.addr base) (offset 1) = val16 (mask15 f) 16 + 2 ^ 255 * (f 15 / 32768) := mf.1
      have hb : val16 (mask15 f) 16 < 2 ^ 255 := mf.2.1
      omega
    rw [he, bitNat_eq mf.2.2.2]

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.DecodeLoad`. -/
section
/-! Merged from `Proof.Ed25519.Arm.CanonicalY`. -/
section
/-! Merged from `Proof.Ed25519.Arm.WordsEqual`. -/
section
/-! Compare bounded fields before modular reduction. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem val16_inj {f g : Nat → Nat} {n : Nat} (hf : ∀ k < n, f k < 65536)
    (hg : ∀ k < n, g k < 65536) : (∀ k < n, f k = g k) ↔ val16 f n = val16 g n := by
  refine ⟨val16_congr, fun h k hk => ?_⟩
  exact (val16_div hf hk).symm.trans ((congrArg (fun x => x / 2 ^ (16 * k) % 65536) h).trans (val16_div hg hk))

structure EqualInv (base : BitVec 32) (a b : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.r2, .r3, .r9] s₀ s
  mem : s.mem = s₀.mem
  zero : s.gpr .r9 = 0#32 ↔ ∀ i < k, limb s₀.mem (State.addr base) a i = limb s₀.mem (State.addr base) b i

theorem equalLimbs_ok {base : BitVec 32} {s₀ : State} (hc : Ctx base s₀) (a b : Nat)
    (ha : a + 64 ≤ 4096) (hb : b + 64 ≤ 4096) (hz : s₀.gpr .r9 = 0#32) :
    WP isa (.block ((List.range 16).flatMap (equalLimb a b))) s₀ fun t =>
      EqualInv base a b s₀ 16 t := by
  refine wp_range_flatMap (M := isa) (EqualInv base a b s₀) (fun k s hk h => ?_) 16 (Nat.le_refl _) s₀
    ⟨Rest.refl _ _, rfl, ⟨fun _ _ h => by omega, fun _ => hz⟩⟩
  have hcs := hc.of_rest h.rest (by decide)
  refine ldr0_ok hcs (by omega) fun s1 u1 =>
    ldr0_ok (hcs.of_rest (u1.rest (ws := [.r3]) (by decide)) (by decide)) (by omega) fun s2 u2 =>
    wp_dp (op2_reg _ _) fun s3 u3 => wp_dp (op2_reg _ _) fun t ht => WP.block_nil ?_
  have el : (s2.gpr .r3).toNat = limb s₀.mem (State.addr base) a k := by
    rw [u2.other _ (by decide), u1.gpr, h.mem]; rfl
  have er : (s2.gpr .r2).toNat = limb s₀.mem (State.addr base) b k := by
    rw [u2.gpr, u1.mem, h.mem]; rfl
  have eqv : s2.gpr .r3 = s2.gpr .r2 ↔ limb s₀.mem (State.addr base) a k = limb s₀.mem (State.addr base) b k :=
    ⟨fun h => el.symm.trans ((congrArg BitVec.toNat h).trans er),
      fun h => BitVec.eq_of_toNat_eq (el.trans (h.trans er.symm))⟩
  refine ⟨h.rest.trans ((u1.rest (by decide)).trans ((u2.rest (by decide)).trans
    ((u3.rest (by decide)).trans (ht.rest (by decide))))), by rw [ht.mem, u3.mem, u2.mem, u1.mem, h.mem], ?_⟩
  rw [ht.gpr]
  change (s3.gpr .r9 ||| s3.gpr .r3 = 0#32) ↔ _
  rw [BitVec.or_eq_zero_iff, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h.zero,
    u3.gpr]
  change (_ ∧ (s2.gpr .r3 ^^^ s2.gpr .r2 = 0#32)) ↔ _
  rw [BitVec.xor_eq_zero_iff, eqv]
  constructor
  · rintro ⟨hpre, hlast⟩ i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hpre i hi
    · exact hlast
  · intro h
    exact ⟨fun i hi => h i (by omega), h k (by omega)⟩

theorem wordsEqual_ok {base : BitVec 32} {s : State} (hc : Ctx base s) (a b : Nat)
    (ha : a + 64 ≤ 4096) (hb : b + 64 ≤ 4096)
    (hla : Lim s.mem (State.addr base) a) (hlb : Lim s.mem (State.addr base) b) :
    WP isa (.block (wordsEqual a b)) s fun t => Rest [.r2, .r3, .r9] s t ∧ t.mem = s.mem ∧
      t.z = decide (V s.mem (State.addr base) a = V s.mem (State.addr base) b) := by
  unfold wordsEqual
  rw [List.append_assoc, WP.block_append_iff]
  refine wp_mov (op2_imm (by decide)) fun u hu => WP.block_nil ?_
  rw [WP.block_append_iff]
  refine WP.mono (equalLimbs_ok (hc.of_rest (hu.rest (ws := [.r9]) (by decide)) (by decide)) a b ha hb hu.gpr)
    fun v hv => ?_
  refine wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
  refine ⟨(hu.rest (by decide)).trans (hv.rest.trans (ht.rest _)), by rw [ht.mem, hv.mem, hu.mem], ?_⟩
  have he : v.gpr .r9 - (0 : BitVec 32) = v.gpr .r9 := BitVec.sub_zero _
  rw [hz, he]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  change (v.gpr .r9 = 0#32) ↔ _
  rw [hv.zero, hu.mem]
  exact val16_inj hla hlb

end VG.Proof.Ed25519.Arm
end

/-! Equality with the canonical representative rejects y >= p. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem canonicalY_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base) :
    WP isa canonicalY s fun t => Keep base s t ∧ AllLim t.mem base ∧ env t.mem base = env s.mem base ∧
      t.z = decide (V s.mem (State.addr base) (offset 1) < Spec.X25519.P) := by
  refine WP.seq (WP.mono (freezeRaw_ok hc hl 1) fun u ⟨uk, ul, ue, uf, uv, uraw⟩ => ?_)
  refine WP.mono (wordsEqual_ok (uk.ctx hc) (offset 1) FR (by decide) (by decide) (ul 1) uf)
    fun t ⟨tr, tm, tz⟩ => ?_
  refine ⟨uk.trans ⟨tr.mono (by decide), by rw [tm]; exact Frame.refl _ _⟩,
    tm ▸ ul, (congrArg (fun m => env m base) tm).trans ue, ?_⟩
  have vy : V u.mem (State.addr base) (offset 1) = V s.mem (State.addr base) (offset 1) :=
    val16_congr (uraw 1)
  rw [tz, vy, uv]
  change decide (V s.mem (State.addr base) (offset 1) = V s.mem (State.addr base) (offset 1) % Spec.X25519.P) = _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    exact h ▸ Nat.mod_lt _ (by decide)
  · intro h
    exact (Nat.mod_eq_of_lt h).symm

end VG.Proof.Ed25519.Arm
end

/-! Read canonical y and the encoded sign from the 32 input bytes. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem packedV_decode (m : Mem) (p : Addr) :
    packedV m p = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32) := by
  rw [decodeLE_eq]
  exact (leNum_bytesAt2 m p 16).symm

theorem pointDecodeLoad_ok {s : State} {base ptr : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (hp : s.gpr .r12 = ptr) (hfit : ptr.toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1)
    (hsep : (⟨State.addr ptr, 32⟩ : Region).Disjoint ⟨State.addr base, 8192⟩) :
    WP isa pointDecodeLoad s fun t => DecodeKeep base s t ∧ AllLim t.mem base ∧
      t.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 =
        BitVec.ofNat 32 (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) / 2 ^ 255 == 1).toNat ∧
      env t.mem base 1 = VG.Proof.X25519.toFe
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) % 2 ^ 255) ∧
      t.z = decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) % 2 ^ 255 < Spec.X25519.P) := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (unpackField_ok hc (o := offset 1) (src := 0) (by decide) (by decide) hp
    (by omega) (by simpa only [Nat.zero_add] using hr) ?_) fun u ⟨ur, uf, ul, uv⟩ => ?_
  · have hp0 : State.addr ptr + BitVec.ofNat 64 0 = State.addr ptr := BitVec.add_zero _
    rw [hp0]
    exact hsep.sub_right (Offset.sub_base _ (by decide))
  have vu : V u.mem (State.addr base) (offset 1) =
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) :=
    uv.trans ((congrArg (packedV s.mem) (BitVec.add_zero _)).trans (packedV_decode _ _))
  obtain ⟨uk, ull, _⟩ := field_finish 1 hl (ur.mono (by decide)) (frame_o uf) ul (v := FS u.mem (State.addr base) (offset 1)) rfl
  refine WP.mono (splitYSign_ok (uk.ctx hc) ull) fun v ⟨vk, vl, vy, vs⟩ => ?_
  have kv : DecodeKeep base s v := (DecodeKeep.of_keep uk).trans vk
  have ve : env v.mem base 1 = VG.Proof.X25519.toFe
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) % 2 ^ 255) :=
    congrArg VG.Proof.X25519.toFe (vy.trans (congrArg (· % 2 ^ 255) vu))
  refine WP.mono (canonicalY_ok (kv.ctx hc) vl) fun t ⟨tk, tl, te, tz⟩ => ?_
  refine ⟨kv.trans (DecodeKeep.of_keep tk), tl, ?_, (congrFun te 1).trans ve, ?_⟩
  · rw [tk.sign, vs, vu]
  · rw [tz, vy, vu]

end VG.Proof.Ed25519.Arm
end

/-! The public byte decoder matches the reviewed strict specification. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

theorem pointDecode_ok {s : State} {base ptr : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (hp : s.gpr .r12 = ptr) (hfit : ptr.toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1)
    (hsep : (⟨State.addr ptr, 32⟩ : Region).Disjoint ⟨State.addr base, 8192⟩) :
    WP isa pointDecode s fun t => DecodeKeep base s t ∧ AllLim t.mem base ∧
      DecodeResult base (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32)) t := by
  have hlen : (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32).length = 32 := by
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]
  refine WP.seq (WP.mono (pointDecodeLoad_ok hc hl hp hfit hr hsep) fun a ⟨ak, al, asign, ay, az⟩ => ?_)
  apply WP.ite (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) % 2 ^ 255 < Spec.X25519.P))
    (by simp only [VG.Arm.eval, az])
  · intro ht
    have hy := of_decide_eq_true ht
    refine WP.mono (recoverPoint_ok (ak.ctx hc) al _ asign) fun t ⟨tk, tl, tr⟩ => ?_
    refine ⟨ak.trans (DecodeKeep.of_ikeep tk), tl, ?_⟩
    rw [decodePoint32 _ hlen, ite_eq_left hy]
    rw [ay] at tr
    exact tr
  · intro hf
    have hy := of_decide_eq_false hf
    refine WP.mono (recoverInvalid_ok a base) fun t ⟨tk, tm, tr⟩ => ?_
    refine ⟨ak.trans (DecodeKeep.of_keep tk), tm ▸ al, ?_⟩
    rw [decodePoint32 _ hlen, ite_eq_right hy]
    exact tr

end VG.Proof.Ed25519.Arm
