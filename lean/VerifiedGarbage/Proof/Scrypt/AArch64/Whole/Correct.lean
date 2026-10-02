import VerifiedGarbage.Proof.Scrypt.AArch64.Whole.Calls

/-!
# scrypt on AArch64: correctness

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/Scrypt/X86_64/Whole/Correct.lean`): step 1 leaves the blocks `X k`
of `PBKDF2-HMAC-SHA256 (P, S, 1, 128 blen)` in `b` (`step1_ok`); the loop
replaces them by their scryptROMix one at a time (`Inv`, `loop_ok`); step 3
derives the key from them (`step3_ok`). `scrypt_ok` puts the frames around
it, for any implementation `pbk` of PBKDF2 verified against its shared
contract.
-/

namespace VG.Proof.Scrypt.AArch64.Whole

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt toNat_add_ofNat)
open VG.Spec.Scrypt (bytesAt)

variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

/-! ## The password, the salt and the blocks -/

namespace Ctx

variable {t : State} (hc : Ctx L g vv m₀ t) (hL : L.Ok)
include hc hL

theorem pw_bytes : bytesAt t.mem L.pw L.pwl.toNat = bytesAt m₀ L.pw L.pwl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.pb, hL.pv, hL.pc, hL.po, hL.kp.symm]) (by have := hL.np; omega)

theorem salt_bytes : bytesAt t.mem L.salt L.sl.toNat = bytesAt m₀ L.salt L.sl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.sb, hL.sv, hL.sc, hL.so, hL.ks.symm]) (by have := hL.ns; omega)

end Ctx

/-- Block `k` of step 1. -/
def X (L : Lay) (m₀ : Mem) (k : Nat) : List Byte :=
  (Spec.Scrypt.blocks (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) L.r.toNat L.pp).getD k []

/-- The derived key of step 1, from the password and the salt on entry. -/
abbrev Step1 (L : Lay) (m₀ : Mem) (B : List Byte) : Prop :=
  Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) 1
    (L.blen.toNat * 128) = some B

theorem X_of (hL : L.Ok) {m : Mem} (h : Step1 L m₀ (bytesAt m L.b (L.blen.toNat * 128))) {k : Nat}
    (hk : k < L.pp) : X L m₀ k = bytesAt m (blkAt L k) (128 * L.r.toNat) := by
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have h' : Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) 1
      (L.pp * 128 * L.r.toNat) = some (bytesAt m L.b (L.pp * 128 * L.r.toNat)) := by rw [e]; exact h
  have hl : k < (Spec.Scrypt.blocks (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat)
      L.r.toNat L.pp).length := by rw [Whole.blocks_length]; exact hk
  rw [X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some,
    Whole.blocks_getElem h' hl]

/-- Distinct blocks are disjoint. -/
theorem blk_disj (hL : L.Ok) {k i : Nat} (hk : k < L.pp) (hi : i < L.pp) (hne : k ≠ i) :
    Region.Disjoint ⟨blkAt L k, 128 * L.r.toNat⟩ ⟨blkAt L i, L.r.toNat * 128⟩ := by
  have h₁ := blk_le hL hk
  have h₂ := blk_le hL hi
  have := hL.nb
  have hr := hL.rpos
  refine Offset.disjoint _ ?_ (by omega) (by omega)
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · left
    have : 128 * L.r.toNat * k + 128 * L.r.toNat ≤ 128 * L.r.toNat * i := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    omega
  · right
    have : 128 * L.r.toNat * i + 128 * L.r.toNat ≤ 128 * L.r.toNat * k := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    omega

theorem blk_sub (hL : L.Ok) {k : Nat} (hk : k < L.pp) :
    Region.Sub ⟨blkAt L k, 128 * L.r.toNat⟩ L.BB := by
  have := blk_le hL hk
  exact Offset.sub_base _ (by omega)

theorem scr_sub (hL : L.Ok) : Region.Sub ⟨L.scr, 200 * 8⟩ L.SC :=
  Within.sub (within_base _ (by have := hL.slen17; omega))

/-! ## Step 1 -/

section
variable {pbk : Prog isa} (hv : Verified AArch64.target pbk (Spec.Hmac.sha256I.pbkdf2Contract AArch64.abi 16))
  (hd : pbk.aarch64Depth ≤ 1) (name : String)
include hv hd

omit hv hd in
theorem pbk1_regions (hL : L.Ok) :
    PbkRegions L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) := by
  have hb := hL.blen_lt
  refine ⟨⟨L.SALT, by simp, within_base _ (Nat.le_refl _)⟩, ?_, ?_, ?_, ?_, hL.ks, hL.ns, ?_, ?_⟩
  · rw [toNat_ofNat_lt hb]; exact .inl (within_base _ (Nat.le_refl _))
  · rw [toNat_ofNat_lt hb]; exact hL.sb
  · exact hL.sc.sub_right (scr_sub hL)
  · rw [toNat_ofNat_lt hb]
    exact hL.bc.sub_right (scr_sub hL)
  · rw [toNat_ofNat_lt hb]; exact hL.nb
  · rw [toNat_ofNat_lt hb]; exact hL.ol1

/-- The call of step 1. -/
theorem pbk1_call_ok (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t)
    (ha : PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t) :
    WP isa (.call name pbk) t fun t' => Ctx L g vv m₀ t' ∧
      Step1 L m₀ (bytesAt t'.mem L.b (L.blen.toNat * 128)) ∧
      ∀ k < L.pp, bytesAt t'.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k := by
  have hb := hL.blen_lt
  refine WP.mono (pbk_call hv hd name hL hc ha (pbk1_regions hL)) fun t₂ ⟨hc₂, _, hp⟩ =>
    ⟨hc₂, ?_, fun k hk => ?_⟩
  · rw [toNat_ofNat_lt hb, hc.pw_bytes hL, hc.salt_bytes hL] at hp
    exact hp
  · rw [toNat_ofNat_lt hb, hc.pw_bytes hL, hc.salt_bytes hL] at hp
    exact (X_of hL hp hk).symm

theorem step1_ok (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) (he : Entry L t) :
    WP isa (pbkCall name pbk pbk1Args) t fun t' => Ctx L g vv m₀ t' ∧
      Step1 L m₀ (bytesAt t'.mem L.b (L.blen.toNat * 128)) ∧
      ∀ k < L.pp, bytesAt t'.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k :=
  WP.seq (WP.mono (pbk1Args_ok hL hc he) fun _ ⟨hc₁, _, ha₁⟩ => pbk1_call_ok hv hd name hL hc₁ ha₁)

end

/-! ## The loop -/

/-- After `i` iterations of the loop: the next block is `i`, and blocks
`0, …, i - 1` are scryptROMix of those of step 1. -/
structure InvB (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.mem.readW (L.B + BitVec.ofNat 64 16) 64 = blkAt L i
  blks : ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) =
    if k < i then Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) else X L m₀ k

abbrev Inv (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (i : Nat) (t : State) :
    Prop :=
  Ctx L g vv m₀ t ∧ InvB L m₀ i t

/-- In iteration `i`, after the call of ROMix: blocks `0, …, i` are scryptROMix
of those of step 1. -/
structure Mid (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.mem.readW (L.B + BitVec.ofNat 64 16) 64 = blkAt L i
  blks : ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) =
    if k < i + 1 then Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) else X L m₀ k

theorem blk_le' (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + 128 * L.r.toNat ≤ L.blen.toNat * 128 := by
  have := blk_le hL hi; rw [Nat.mul_comm L.r.toNat 128] at this; exact this

theorem blk0 (L : Lay) : blkAt L 0 = L.b := by
  simp only [blkAt, Nat.mul_zero]; exact BitVec.add_zero _

/-- A block of `b` misses the frame's first word. -/
theorem blk_fr (hL : L.Ok) {k : Nat} (hk : k < L.pp) :
    Region.Disjoint ⟨blkAt L k, 128 * L.r.toNat⟩ ⟨L.B + BitVec.ofNat 64 16, 8⟩ :=
  (hL.kb.symm.sub_left (blk_sub hL hk)).sub_right (Offset.sub_base _ (by omega))

theorem start_ok (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t)
    (hx : ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k) :
    WP isa (.block cur0) t (Inv L g vv m₀ 0) :=
  WP.mono (cur0_ok hL hc) fun t' ⟨hc', hb, hf⟩ => ⟨hc', hb.trans (blk0 L).symm, fun k hk => by
    simp only [Nat.not_lt_zero, ite_false]
    rw [← hx k hk]
    exact Memory.frame_bytesAt hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact blk_fr hL hk)
      (by have := hL.blen_lt; have := blk_le hL hk; omega)⟩

theorem next_eq (L : Lay) (i : Nat) :
    blkAt L i + BitVec.ofNat 64 (L.r.toNat * 128) = blkAt L (i + 1) := by
  simp only [blkAt]
  rw [add_add, Nat.mul_succ (128 * L.r.toNat) i, Nat.mul_comm L.r.toNat 128]

/-- The bytes of `b` left after block `i`, as the loop's condition reads them. -/
theorem left_eq (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    (L.b + BitVec.ofNat 64 (L.blen.toNat * 128) - blkAt L (i + 1) != 0) = decide (i + 1 ≠ L.pp) := by
  have h₁ := blk_le hL hi
  have hb := hL.blen_lt
  have hr := hL.rpos
  simp only [blkAt]
  rw [Offset.add_sub_add_left, ← hL.len_b]
  have e₁ : 128 * L.r.toNat * (i + 1) < 2 ^ 64 := by
    rw [Nat.mul_succ]; rw [← hL.len_b] at h₁ hb; omega
  have e₂ : 128 * L.r.toNat * L.pp < 2 ^ 64 := by rw [hL.len_b]; exact hb
  rw [bne, Offset.ofNat_sub_ofNat_beq e₂ e₁, decide_not]
  refine congrArg (!·) (decide_eq_decide.mpr ⟨fun h => ?_, fun h => by rw [h]⟩)
  exact (Nat.eq_of_mul_eq_mul_left (by omega) h).symm

theorem call_step (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (hc : Ctx L g vv m₀ t)
    (hb : InvB L m₀ i t) (ha : RomixArgs L (blkAt L i) t) :
    WP isa (.call "vg_scrypt_romix" Impl.Scrypt.AArch64.roMix) t fun t' =>
      Ctx L g vv m₀ t' ∧ Mid L m₀ i t' := by
  have hnB := hL.nB
  refine WP.mono (romix_call hL hc hi ha) fun t₂ ⟨hc₂, hf₂, hr₂⟩ => ⟨hc₂, ?_, fun k hk => ?_⟩
  · rw [← hb.cur]
    refine hf₂.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hL.stk_in (by omega) (blk_in hL hi)
    · exact hL.stk_in (by omega) (.inr (.inl (within_base _ (Nat.le_refl _))))
    · exact hL.stk_in (by omega) (.inr (.inr (.inl (within_base _ (by have := hL.slen; omega)))))
    · exact Offset.disjoint_base _ (by omega) (by omega)
  · by_cases hki : k = i
    · subst hki
      rw [hr₂, hb.blks k hk]
      simp only [Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
    · have e₂ : bytesAt t₂.mem (blkAt L k) (128 * L.r.toNat) = bytesAt t.mem (blkAt L k) (128 * L.r.toNat) :=
        Memory.frame_bytesAt hf₂ (fun r hr => by
          simp only [romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact blk_disj hL hk hi hki
          · exact hL.bv.sub_left (blk_sub hL hk)
          · exact (hL.bc.sub_left (blk_sub hL hk)).sub_right
              (Within.sub (within_base _ (by have := hL.slen; omega)))
          · exact (hL.kb.symm.sub_left (blk_sub hL hk)).sub_right (Region.sub_prefix (by omega)))
          (by have := hL.blen_lt; have := blk_le hL hk; omega)
      rw [e₂, hb.blks k hk]
      by_cases hlt : k < i
      · have : k < i + 1 := by omega
        simp only [hlt, this, ite_true]
      · have : ¬ k < i + 1 := by omega
        simp only [hlt, this, ite_false]

theorem next_step (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (hc : Ctx L g vv m₀ t)
    (hm : Mid L m₀ i t) :
    WP isa (.block nextBlock) t fun t' => Ctx L g vv m₀ t' ∧ InvB L m₀ (i + 1) t' ∧
      (t'.gpr .x11 != 0) = decide (i + 1 ≠ L.pp) :=
  WP.mono (nextBlock_ok hL hc hm.cur) fun t₃ ⟨hc₃, hf₃, hb₃, hx₃⟩ =>
    ⟨hc₃, ⟨by rw [hb₃, next_eq], fun k hk => by
      rw [← hm.blks k hk]
      exact Memory.frame_bytesAt hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact blk_fr hL hk)
        (by have := hL.blen_lt; have := blk_le hL hk; omega)⟩,
      by rw [hx₃, next_eq, left_eq hL hi]⟩

theorem body_ok (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (h : Inv L g vv m₀ i t) :
    WP isa (.seq (.block romixArgs) (.seq (.call "vg_scrypt_romix" Impl.Scrypt.AArch64.roMix)
      (.block nextBlock))) t fun t' =>
        Inv L g vv m₀ (i + 1) t' ∧ (t'.gpr .x11 != 0) = decide (i + 1 ≠ L.pp) :=
  WP.seq (WP.mono (romixArgs_ok hL h.1 h.2.cur) fun t₁ ⟨hc₁, hm₁, ha₁⟩ =>
    WP.seq (WP.mono (call_step hL hi hc₁ ⟨by rw [hm₁]; exact h.2.cur, by rw [hm₁]; exact h.2.blks⟩ ha₁)
      fun t₂ ⟨hc₂, hm₂⟩ => WP.mono (next_step hL hi hc₂ hm₂) fun _ ⟨hc₃, hb₃, hz₃⟩ => ⟨⟨hc₃, hb₃⟩, hz₃⟩))

theorem loop_ok (hL : L.Ok) {t : State} (h : Inv L g vv m₀ 0 t) :
    WP isa romixLoop t (Inv L g vv m₀ L.pp) :=
  RoMix.count_loop hL.pp_pos (Inv L g vv m₀) (fun _ hi _ h => body_ok hL hi h) h

/-! ## Step 3 -/

section
variable {pbk : Prog isa} (hv : Verified AArch64.target pbk (Spec.Hmac.sha256I.pbkdf2Contract AArch64.abi 16))
  (hd : pbk.aarch64Depth ≤ 1) (name : String)
include hv hd

omit hv hd in
/-- The blocks after the loop, as one string. -/
theorem final_bytes' (hL : L.Ok) {t : State} (h : Inv L g vv m₀ L.pp t) :
    bytesAt t.mem L.b (L.blen.toNat * 128) =
      (List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) := by
  rw [← hL.len_b, Whole.bytesAt_chunks]
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [h.2.blks k hk]; simp only [hk, ite_true]

omit hv hd in
theorem pbk2_regions (hL : L.Ok) :
    PbkRegions L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol := by
  have hb := hL.blen_lt
  refine ⟨⟨L.BB, by simp, ?_⟩, .inr (.inr (.inr (within_base _ (Nat.le_refl _)))), ?_,
    ?_, hL.co.symm.sub_right (scr_sub hL), ?_, ?_, hL.no, hL.olb⟩
  · rw [toNat_ofNat_lt hb]; exact within_base _ (Nat.le_refl _)
  · rw [toNat_ofNat_lt hb]; exact hL.bo
  · rw [toNat_ofNat_lt hb]; exact hL.bc.sub_right (scr_sub hL)
  · rw [toNat_ofNat_lt hb]; exact hL.kb
  · rw [toNat_ofNat_lt hb]; exact hL.nb

theorem step3_ok (hL : L.Ok) {t : State} (h : Inv L g vv m₀ L.pp t) :
    WP isa (pbkCall name pbk pbk2Args) t fun t' => Ctx L g vv m₀ t' ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ L.pw L.pwl.toNat)
        ((List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k)) 1 L.ol.toNat =
        some (bytesAt t'.mem L.out L.ol.toNat) := by
  have hb := hL.blen_lt
  refine WP.seq (WP.mono (pbk2Args_ok hL h.1) fun t₁ ⟨hc₁, hm₁, ha₁⟩ => ?_)
  refine WP.mono (pbk_call hv hd name hL hc₁ ha₁ (pbk2_regions hL)) fun t₂ ⟨hc₂, _, hp⟩ => ⟨hc₂, ?_⟩
  rw [toNat_ofNat_lt hb, hc₁.pw_bytes hL, hm₁, final_bytes' hL h] at hp
  exact hp

/-- The inner frame's body, once our arguments are saved. -/
theorem rest_ok (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) (he : Entry L t) :
    WP isa (.seq (pbkCall name pbk pbk1Args) (.seq (.block cur0) (.seq romixLoop (pbkCall name pbk pbk2Args))))
      t fun t' => Ctx L g vv m₀ t' ∧
      Spec.Scrypt.scrypt (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) L.NN L.r.toNat L.pp
        L.ol.toNat = some (bytesAt t'.mem L.out L.ol.toNat) := by
  refine WP.seq (WP.mono (step1_ok hv hd name hL hc he) fun t₁ ⟨hc₁, h1, hx⟩ => ?_)
  refine WP.seq (WP.mono (start_ok hL hc₁ hx) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (loop_ok hL h₂) fun t₃ h₃ => ?_)
  refine WP.mono (step3_ok hv hd name hL h₃) fun t₄ ⟨hc₄, hp⟩ => ⟨hc₄, ?_⟩
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  refine Whole.scrypt_eq hL.valid (B := bytesAt t₁.mem L.b (L.blen.toNat * 128)) (by rw [e]; exact h1) ?_
  refine Eq.trans (congrArg (fun x => Spec.Pbkdf2.pbkdf2HmacSha256 _ x 1 _) ?_) hp
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [X_of hL h1 hk, Whole.chunk_bytesAt _ _ (blk_le' hL hk)]

end

/-! ## The whole function -/

section
variable {pbk : Prog isa} (hv : Verified AArch64.target pbk (Spec.Hmac.sha256I.pbkdf2Contract AArch64.abi 16))
  (hd : pbk.aarch64Depth ≤ 1) (name : String)
include hv hd

/-- `vg_scrypt` meets `scryptAArch64` and the calling convention. -/
theorem scrypt_ok {s : State} (h : Proof.Scrypt.scryptAArch64.pre s) :
    WP isa (scrypt name pbk) s fun s' => abiPreserved s s' ∧ Proof.Scrypt.scryptAArch64.post s s' := by
  have hL := lay_ok h
  have h96 := h.1
  refine WP.frame (by omega) (WP.alloc (by decide) ?_ ?_)
  · show 64 ≤ (s.sp - 16).toNat
    rw [BitVec.toNat_sub_of_le (by show 16 ≤ s.sp.toNat; omega)]
    show 64 ≤ s.sp.toNat - 16
    omega
  · show WP isa (scryptBody name pbk) (entered s) _
    refine WP.seq (WP.mono (entry_ok h) fun t ⟨hc, he⟩ => ?_)
    refine WP.mono (rest_ok hv hd name hL hc he) fun u ⟨hu, ho⟩ => ?_
    have lr : u.mem.read (u.sp + BitVec.ofNat 64 64) 8 = s.gpr .x30 := by
      rw [hu.sp, add_add, read8]; exact hu.kept.lr
    refine ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ho⟩
    · show ((freed 64 u).write .x .x30 (u.mem.read (u.sp + BitVec.ofNat 64 64) 8)).gpr r = _
      rw [lr, RegUpd.gpr_write]
      by_cases h30 : r = .x30
      · subst r; simp only [ite_true, BitVec.setWidth_eq]
      · simp only [h30, ite_false]
        exact hu.cs r hr h30
    · show u.sp + BitVec.ofNat 64 64 + BitVec.ofNat 64 16 = s.sp
      rw [hu.sp, add_add, add_add]
      exact lay_top s
    · show (((freed 64 u).write .x .x30 (u.mem.read (u.sp + BitVec.ofNat 64 64) 8)).v r).extractLsb' 0 64 = _
      rw [RegUpd.v_write]
      exact hu.vs r hr

end

end VG.Proof.Scrypt.AArch64.Whole
