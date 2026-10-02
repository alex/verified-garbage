import VerifiedGarbage.Proof.Scrypt.Arm.Whole.Calls

/-!
# scrypt on 32-bit ARM: correctness

Untrusted: everything here is checked by Lean. As on the other targets
(`Proof/Scrypt/AArch64/Whole/Correct.lean`): our caller's registers are
saved (`entry_ok`); step 1 leaves the blocks `X k` of
`PBKDF2-HMAC-SHA256 (P, S, 1, 128 blen)` in `b` (`step1_ok`); the loop
replaces them by their scryptROMix one at a time (`Inv`, `loop_ok`); step 3
derives the key from them (`step3_ok`); our caller's registers are restored
(`scrypt_ok`).
-/

namespace VG.Proof.Scrypt.Arm.Whole

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Arm.FrameStack
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt toNat_add_ofNat)
open VG.Spec.Scrypt (bytesAt)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem}

theorem t32 {x : Nat} (h : x < 2 ^ 32) : (BitVec.ofNat 32 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-! ## The password, the salt and the blocks -/

namespace Ctx

variable {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok)
include hc hL

theorem pw_bytes : bytesAt t.mem (State.addr L.pw) L.pwl.toNat = bytesAt m₀ (State.addr L.pw) L.pwl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.pb, hL.pv, hL.pc, hL.po, hL.kp.symm]) (by have := L.pwl.isLt; omega)

theorem salt_bytes : bytesAt t.mem (State.addr L.salt) L.sl.toNat = bytesAt m₀ (State.addr L.salt) L.sl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.sb, hL.sv, hL.sc, hL.so, hL.ks.symm]) (by have := L.sl.isLt; omega)

end Ctx

/-- Block `k` of step 1. -/
def X (L : Lay) (m₀ : Mem) (k : Nat) : List Byte :=
  (Spec.Scrypt.blocks (bytesAt m₀ (State.addr L.pw) L.pwl.toNat) (bytesAt m₀ (State.addr L.salt) L.sl.toNat)
    L.r.toNat L.pp).getD k []

/-- The derived key of step 1, from the password and the salt on entry. -/
abbrev Step1 (L : Lay) (m₀ : Mem) (B : List Byte) : Prop :=
  Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (State.addr L.pw) L.pwl.toNat)
    (bytesAt m₀ (State.addr L.salt) L.sl.toNat) 1 (L.blen.toNat * 128) = some B

theorem X_of (hL : L.Ok) {m : Mem} (h : Step1 L m₀ (bytesAt m (State.addr L.b) (L.blen.toNat * 128))) {k : Nat}
    (hk : k < L.pp) : X L m₀ k = bytesAt m (blkA L k) (128 * L.r.toNat) := by
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have h' : Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (State.addr L.pw) L.pwl.toNat)
      (bytesAt m₀ (State.addr L.salt) L.sl.toNat) 1 (L.pp * 128 * L.r.toNat) =
      some (bytesAt m (State.addr L.b) (L.pp * 128 * L.r.toNat)) := by rw [e]; exact h
  have hl : k < (Spec.Scrypt.blocks (bytesAt m₀ (State.addr L.pw) L.pwl.toNat)
      (bytesAt m₀ (State.addr L.salt) L.sl.toNat) L.r.toNat L.pp).length := by
    rw [Whole.blocks_length]; exact hk
  rw [X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some,
    Whole.blocks_getElem h' hl]

/-- Distinct blocks are disjoint. -/
theorem blk_disj (hL : L.Ok) {k i : Nat} (hk : k < L.pp) (hi : i < L.pp) (hne : k ≠ i) :
    Region.Disjoint ⟨blkA L k, 128 * L.r.toNat⟩ ⟨blkA L i, L.r.toNat * 128⟩ := by
  have h₁ := blk_le hL hk
  have h₂ := blk_le hL hi
  have := hL.blen_lt
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
    Region.Sub ⟨blkA L k, 128 * L.r.toNat⟩ L.BB := by
  have := blk_le hL hk
  exact Offset.sub_base _ (by omega)

theorem blk_le' (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + 128 * L.r.toNat ≤ L.blen.toNat * 128 := by
  have := blk_le hL hi; rw [Nat.mul_comm L.r.toNat 128] at this; exact this

theorem blk0 (L : Lay) : blkAt L 0 = L.b := by
  simp only [blkAt, Nat.mul_zero]; exact BitVec.add_zero _

/-! ## Entry -/

/-- The state on entry. -/
theorem entry_E {s : State} (h : Proof.Scrypt.scryptArm.pre s) : E (lay s) s.gpr s.mem s := by
  have hL := lay_ok h
  have a : ∀ k, k + 4 ≤ 36 → s.mem.readW (State.addr (lay s).sp + BitVec.ofNat 64 k) 32 =
      s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 k)) 32 := fun k hk => by
    rw [← hL.arg_addr hk]; rfl
  refine ⟨?_, h.2.2.2.1, rfl, fun _ _ _ => rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Frame.refl _ _, rfl, rfl,
    rfl, rfl⟩
  · rw [h.2.2.1, ← lay_args]; rfl
  all_goals (rw [a _ (by omega)]; rfl)

/-! ## Step 1 -/

section
variable {pbk : Prog isa} (hv : Verified Arm.target pbk (Spec.Hmac.sha256I.pbkdf2Contract Arm.abi 24))
  (hst : armStack pbk ≤ 24) (name : String)
include hv hst

omit hv hst in
theorem scr_sub (hL : L.Ok) : Region.Sub (scr1600 L) L.SC :=
  Within.sub (within_base _ (by have := hL.slen17; omega))

omit hv hst in
theorem pbk1_regions (hL : L.Ok) :
    PbkRegions L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) := by
  have hb := hL.blen_lt
  have e : (BitVec.ofNat 32 (L.blen.toNat * 128)).toNat = L.blen.toNat * 128 := t32 hb
  refine ⟨⟨L.SALT, by simp, within_base _ (Nat.le_refl _)⟩, ?_, ?_, ?_, hL.sc.sub_right (scr_sub hL), ?_,
    hL.ks, hL.ns, ?_, ?_⟩
  · rw [e]; exact .inl (within_base _ (Nat.le_refl _))
  · rw [e]; exact (hL.bc.sub_right hL.sv_sc)
  · rw [e]; exact hL.sb
  · rw [e]; exact hL.bc.sub_right (scr_sub hL)
  · rw [e]; exact hL.nb
  · rw [e]; exact hL.ol1

theorem step1_ok (hL : L.Ok) {t₁ : State} (hc₁ : Ctx L g m₀ t₁) (h4 : t₁.gpr .r4 = L.b)
    (ha₁ : PbkArgs L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) t₁) :
    WP isa (pbkCall name pbk) t₁ fun t' => Ctx L g m₀ t' ∧
      t'.gpr .r4 = L.b ∧ Step1 L m₀ (bytesAt t'.mem (State.addr L.b) (L.blen.toNat * 128)) ∧
      ∀ k < L.pp, bytesAt t'.mem (blkA L k) (128 * L.r.toNat) = X L m₀ k := by
  have hb := hL.blen_lt
  refine WP.mono (pbk_call hv hst name hL hc₁ ha₁ (pbk1_regions hL)) fun t₂ ⟨hc₂, h4₂, _, hp⟩ =>
    ⟨hc₂, h4₂.trans h4, ?_, fun k hk => ?_⟩
  · rw [t32 hb, hc₁.pw_bytes hL, hc₁.salt_bytes hL] at hp
    exact hp
  · rw [t32 hb, hc₁.pw_bytes hL, hc₁.salt_bytes hL] at hp
    exact (X_of hL hp hk).symm

end

/-! ## The loop -/

/-- After `i` iterations of the loop: the next block is `i`, and blocks
`0, …, i - 1` are scryptROMix of those of step 1. -/
structure InvB (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.gpr .r4 = blkAt L i
  blks : ∀ k < L.pp, bytesAt t.mem (blkA L k) (128 * L.r.toNat) =
    if k < i then Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) else X L m₀ k

abbrev Inv (L : Lay) (g : Reg → BitVec 32) (m₀ : Mem) (i : Nat) (t : State) : Prop :=
  Ctx L g m₀ t ∧ InvB L m₀ i t

/-- In iteration `i`, after the call of ROMix: blocks `0, …, i` are scryptROMix
of those of step 1. -/
structure Mid (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.gpr .r4 = blkAt L i
  blks : ∀ k < L.pp, bytesAt t.mem (blkA L k) (128 * L.r.toNat) =
    if k < i + 1 then Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) else X L m₀ k

theorem next_eq (L : Lay) (i : Nat) :
    blkAt L i + BitVec.ofNat 32 (L.r.toNat * 128) = blkAt L (i + 1) := by
  simp only [blkAt]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_succ (128 * L.r.toNat) i, Nat.mul_comm L.r.toNat 128]

theorem z_eq (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    (blkAt L (i + 1) - (L.b + BitVec.ofNat 32 (L.blen.toNat * 128)) == 0) = decide (i + 1 = L.pp) := by
  have h₁ := blk_le hL hi
  have hb := hL.blen_lt
  have hr := hL.rpos
  simp only [blkAt]
  rw [Offset.add_sub_add_left, ← hL.len_b]
  have e₁ : 128 * L.r.toNat * (i + 1) < 2 ^ 32 := by
    rw [Nat.mul_succ]; rw [← hL.len_b] at h₁ hb; omega
  have e₂ : 128 * L.r.toNat * L.pp < 2 ^ 32 := by rw [hL.len_b]; exact hb
  rw [VG.Proof.MdStream.Arm.sub_beq e₁ e₂]
  refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => by rw [h]⟩
  exact Nat.eq_of_mul_eq_mul_left (by omega) h

theorem call_step (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (hc : Ctx L g m₀ t)
    (hb : InvB L m₀ i t) (ha : RomixArgs L (blkAt L i) t) :
    WP isa (.frame (.push [.r12, .lr]) (.call "vg_scrypt_romix" Impl.Scrypt.Arm.roMix) (.pop .r12 8)) t
      fun t' => Ctx L g m₀ t' ∧ Mid L m₀ i t' := by
  refine WP.mono (romix_call hL hc hi ha) fun t₂ ⟨hc₂, h4, hf₂, hr₂⟩ => ⟨hc₂, h4.trans hb.cur, fun k hk => ?_⟩
  by_cases hki : k = i
  · subst hki
    rw [hr₂, hb.blks k hk]
    simp only [Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
  · have e₂ : bytesAt t₂.mem (blkA L k) (128 * L.r.toNat) = bytesAt t.mem (blkA L k) (128 * L.r.toNat) :=
      Memory.frame_bytesAt hf₂ (fun r hr => by
        simp only [romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact blk_disj hL hk hi hki
        · exact hL.bv.sub_left (blk_sub hL hk)
        · exact (hL.bc.sub_left (blk_sub hL hk)).sub_right
            (Within.sub (within_base _ (by have := hL.slen; omega)))
        · exact (hL.kb.symm.sub_left (blk_sub hL hk)))
        (by have := hL.blen_lt; have := blk_le hL hk; omega)
    rw [e₂, hb.blks k hk]
    by_cases hlt : k < i
    · have : k < i + 1 := by omega
      simp only [hlt, this, ite_true]
    · have : ¬ k < i + 1 := by omega
      simp only [hlt, this, ite_false]

theorem body_ok (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (h : Inv L g m₀ i t) :
    WP isa (.seq (.block romixArgs) (.seq (.frame (.push [.r12, .lr]) (.call "vg_scrypt_romix"
      Impl.Scrypt.Arm.roMix) (.pop .r12 8)) (.block nextBlock))) t fun t' =>
        Inv L g m₀ (i + 1) t' ∧ t'.z = decide (i + 1 = L.pp) := by
  refine WP.seq (WP.mono (romixArgs_ok hL h.1) fun t₁ ⟨hc₁, hm₁, h4₁, ha₁⟩ => ?_)
  rw [h.2.cur] at ha₁
  refine WP.seq (WP.mono (call_step hL hi hc₁ ⟨h4₁.trans h.2.cur, by rw [hm₁]; exact h.2.blks⟩ ha₁)
    fun t₂ ⟨hc₂, hm₂⟩ => ?_)
  refine WP.mono (nextBlock_ok hc₂) fun t₃ ⟨hc₃, hm₃, h4₃, hz₃⟩ =>
    ⟨⟨hc₃, ⟨by rw [h4₃, hm₂.cur, next_eq], by rw [hm₃]; exact hm₂.blks⟩⟩, ?_⟩
  rw [hz₃, hm₂.cur, next_eq, z_eq hL hi]

theorem loop_ok (hL : L.Ok) {t : State} (h : Inv L g m₀ 0 t) : WP isa romixLoop t (Inv L g m₀ L.pp) :=
  RoMix.count_loop hL.pp_pos (Inv L g m₀) (fun _ hi _ h => body_ok hL hi h) h

/-! ## Step 3 -/

section
variable {pbk : Prog isa} (hv : Verified Arm.target pbk (Spec.Hmac.sha256I.pbkdf2Contract Arm.abi 24))
  (hst : armStack pbk ≤ 24) (name : String)
include hv hst

omit hv hst in
/-- The blocks after the loop, as one string. -/
theorem final_bytes' (hL : L.Ok) {t : State} (h : Inv L g m₀ L.pp t) :
    bytesAt t.mem (State.addr L.b) (L.blen.toNat * 128) =
      (List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) := by
  rw [← hL.len_b, Whole.bytesAt_chunks]
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [h.2.blks k hk]; simp only [hk, ite_true]

omit hv hst in
theorem pbk2_regions (hL : L.Ok) :
    PbkRegions L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol := by
  have hb := hL.blen_lt
  have e : (BitVec.ofNat 32 (L.blen.toNat * 128)).toNat = L.blen.toNat * 128 := t32 hb
  have sc : Region.Sub (scr1600 L) L.SC := Within.sub (within_base _ (by have := hL.slen17; omega))
  refine ⟨⟨L.BB, by simp, ?_⟩, .inr (.inr (.inr (within_base _ (Nat.le_refl _)))),
    hL.co.symm.sub_right hL.sv_sc, ?_, ?_, hL.co.symm.sub_right sc, ?_, ?_, hL.no, hL.olb⟩
  · rw [e]; exact within_base _ (Nat.le_refl _)
  · rw [e]; exact hL.bo
  · rw [e]; exact hL.bc.sub_right sc
  · rw [e]; exact hL.kb
  · rw [e]; exact hL.nb

theorem step3_ok (hL : L.Ok) {t t₁ : State} (h : Inv L g m₀ L.pp t) (hc₁ : Ctx L g m₀ t₁)
    (hm₁ : t₁.mem = t.mem) (ha₁ : PbkArgs L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol t₁) :
    WP isa (pbkCall name pbk) t₁ fun t' => Ctx L g m₀ t' ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (State.addr L.pw) L.pwl.toNat)
        ((List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k)) 1 L.ol.toNat =
        some (bytesAt t'.mem (State.addr L.out) L.ol.toNat) := by
  have hb := hL.blen_lt
  refine WP.mono (pbk_call hv hst name hL hc₁ ha₁ (pbk2_regions hL)) fun t₂ ⟨hc₂, _, _, hp⟩ => ⟨hc₂, ?_⟩
  rw [t32 hb, hc₁.pw_bytes hL, hm₁, final_bytes' hL h] at hp
  exact hp

end

/-! ## The whole function -/

/-- scrypt, from the two derivations and the blocks. -/
theorem body_post (hL : L.Ok) {m : Mem} {out : List Byte}
    (h1 : Step1 L m₀ (bytesAt m (State.addr L.b) (L.blen.toNat * 128)))
    (hp : Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (State.addr L.pw) L.pwl.toNat)
      ((List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k)) 1 L.ol.toNat = some out) :
    Spec.Scrypt.scrypt (bytesAt m₀ (State.addr L.pw) L.pwl.toNat) (bytesAt m₀ (State.addr L.salt) L.sl.toNat)
      L.NN L.r.toNat L.pp L.ol.toNat = some out := by
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  refine Whole.scrypt_eq hL.valid (B := bytesAt m (State.addr L.b) (L.blen.toNat * 128)) (by rw [e]; exact h1) ?_
  refine Eq.trans (congrArg (fun x => Spec.Pbkdf2.pbkdf2HmacSha256 _ x 1 _) ?_) hp
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [X_of hL h1 hk, Whole.chunk_bytesAt _ _ (blk_le' hL hk)]

section
variable {pbk : Prog isa} (hv : Verified Arm.target pbk (Spec.Hmac.sha256I.pbkdf2Contract Arm.abi 24))
  (hst : armStack pbk ≤ 24) (name : String)
include hv hst

/-- `vg_scrypt` meets `scryptArm` and the calling convention. -/
theorem scrypt_ok {s : State} (h : Proof.Scrypt.scryptArm.pre s) :
    WP isa (scrypt name pbk) s fun s' => abiPreserved s s' ∧ Proof.Scrypt.scryptArm.post s s' := by
  have hL := lay_ok h
  refine WP.seq (WP.mono (save1_ok hL (entry_E h) rfl) fun t₁ ⟨e₁, _, r₁, w₁⟩ => ?_)
  refine WP.seq (WP.mono (save2_ok hL e₁ r₁ w₁) fun t₂ ⟨e₂, r₂, w₂, s₂⟩ => ?_)
  refine WP.seq (WP.mono (save3_ok hL e₂ r₂ w₂ s₂) fun t₃ ⟨e₃, s₃⟩ => ?_)
  refine WP.seq (WP.mono (pbk1Args_ok hL e₃ s₃) fun t₄ ⟨hc₄, _, h4₄, ha₄⟩ => ?_)
  refine WP.seq (WP.mono (step1_ok hv hst name hL hc₄ h4₄ ha₄) fun t₅ ⟨hc₅, h4₅, h1, hx⟩ => ?_)
  have i0 : Inv (lay s) s.gpr s.mem 0 t₅ := ⟨hc₅, by rw [h4₅, blk0], fun k hk => by
    rw [hx k hk]; simp only [Nat.not_lt_zero, ite_false]⟩
  refine WP.seq (WP.mono (loop_ok hL i0) fun t₆ h₆ => ?_)
  refine WP.seq (WP.mono (pbk2Args_ok hL h₆.1) fun t₇ ⟨hc₇, hm₇, ha₇⟩ => ?_)
  refine WP.seq (WP.mono (step3_ok hv hst name hL h₆ hc₇ hm₇ ha₇) fun t₈ ⟨hc₈, hp⟩ => ?_)
  refine WP.mono (restore_ok hL hc₈) fun t₉ ⟨hr₉, hsp₉, hm₉⟩ => ⟨⟨hr₉, hsp₉.trans hc₈.sp⟩, ?_⟩
  simp only [Proof.Scrypt.scryptArm, hm₉]
  exact body_post hL h1 hp

end

end VG.Proof.Scrypt.Arm.Whole
