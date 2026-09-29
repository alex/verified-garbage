import VerifiedGarbage.Proof.Pbkdf2.Arm.Body
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Spec.Pbkdf2.Contract

/-!
# PBKDF2-HMAC-SHA-256's iteration on ARMv7

Untrusted: everything here is checked by Lean. The prologue, the epilogue,
and `Verified`. Constant time is proven by the taint analysis: `t` (in `r0`
around the calls) and the scratch space (in `r3`) are the bases of the two
writable regions, so the registers `vg_sha256_compress` saves in its scratch
space and restores are known to keep their public values.
-/

namespace VG.Proof.Pbkdf2.Arm

open VG VG.Arm VG.Impl.Pbkdf2.Arm
open VG.Impl.Sha256.Arm.Stream (saved restore save)
open VG.Impl.Hmac.Arm (cp)
open VG.Proof.Sha256.Arm (contains_offset)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_str wp_ldrSp wp_cmp op2_imm op2_reg saveMem)
open VG.Proof.Sha256.Arm.Stream (save_ok restore_ok saveMem_saved saveMem_frame saved_bound)
open VG.Proof.MdStream.Arm (addr_toNat)
open VG.Proof.Hmac.Arm (copy_ok)
open VG.Proof.Hmac.Arm.Init (beq_zero_toNat)
open VG.Proof.Hmac.X86_64 (bytesAt_length bytesAt_writeBytes_self bytesAt_writeBytes_sep)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame writeBytes_nil)
open VG.Proof.Pbkdf2.Memory (frame_bytesAt contains_base writeW_bytes writeBytes_append' iterate_congr
  add_ofNat)
open VG.Spec.Sha256 (bytesAt stateAt Repr)
open VG.Spec.Hmac (xorPad ipad opad hmacBlockKey sha256)

/-! ## The padding -/

/-- A word stored right after bytes written before. -/
theorem writeW_append (m : Mem) (q : Addr) (xs ys : List Byte) (v : BitVec 32) {a : Addr}
    (ha : a = q + BitVec.ofNat 64 xs.length)
    (hv : ((List.range (32 / 8)).map fun j => (v.setWidth (8 * (32 / 8))).extractLsb' (8 * j) 8) = ys)
    (hl : xs.length + ys.length < 2 ^ 64) :
    (writeBytes m q xs).writeW a v = writeBytes m q (xs ++ ys) := by
  rw [writeW_bytes _ _ v ys hv, writeBytes_append' _ _ _ ha hl]

/-- A store of `r12` at `[r3, #d]`, within the scratch space. -/
theorem str_ok {s₀ : State} (hp : Pre s₀) {s : State} (h3 : s.gpr .r3 = scr s₀) (hwr : s.wr = s₀.wr)
    {d : Nat} (hd : d + 4 ≤ 384) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Mupd s s' (s.mem.writeW (scA s₀ + BitVec.ofNat 64 d) (s.gpr .r12)) → WP isa (.block rest) s' Q) :
    WP isa (.block (.str .r12 .r3 d :: rest)) s Q :=
  wp_str (by omega) (by rw [h3]; exact scr_add hp (by omega)) (in_scr hp hwr hd) k

/-- The padding into `scratch[224..256)`. -/
theorem padding_ok {s₀ : State} (hp : Pre s₀) {s : State} (h3 : s.gpr .r3 = scr s₀) (hwr : s.wr = s₀.wr)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (scA s₀ + BitVec.ofNat 64 224) pad96 → WP isa (.block rest) s' Q) :
    WP isa (.block (padding ++ rest)) s Q := by
  simp only [padding, List.cons_append, List.nil_append]
  let P := scA s₀ + BitVec.ofNat 64 224
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  have c₁ : s₁.gpr .r3 = scr s₀ := by rw [u₁.other _ (by decide), h3]
  refine str_ok hp c₁ (u₁.wr.trans hwr) (d := 224) (by omega) fun s₂ g₂ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₃ u₃ => ?_
  have c₃ : s₃.gpr .r3 = scr s₀ := by rw [u₃.other _ (by decide), g₂.gpr, c₁]
  have w₃ : s₃.wr = s₀.wr := by rw [u₃.wr, g₂.wr, u₁.wr, hwr]
  have z₃ : s₃.gpr .r12 = 0 := u₃.gpr
  refine str_ok hp c₃ w₃ (d := 228) (by omega) fun s₄ g₄ => ?_
  refine str_ok hp (by rw [g₄.gpr, c₃]) (by rw [g₄.wr, w₃]) (d := 232) (by omega) fun s₅ g₅ => ?_
  refine str_ok hp (by rw [g₅.gpr, g₄.gpr, c₃]) (by rw [g₅.wr, g₄.wr, w₃]) (d := 236) (by omega) fun s₆ g₆ => ?_
  refine str_ok hp (by rw [g₆.gpr, g₅.gpr, g₄.gpr, c₃]) (by rw [g₆.wr, g₅.wr, g₄.wr, w₃]) (d := 240) (by omega)
    fun s₇ g₇ => ?_
  refine str_ok hp (by rw [g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, c₃]) (by rw [g₇.wr, g₆.wr, g₅.wr, g₄.wr, w₃])
    (d := 244) (by omega) fun s₈ g₈ => ?_
  refine str_ok hp (by rw [g₈.gpr, g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, c₃])
    (by rw [g₈.wr, g₇.wr, g₆.wr, g₅.wr, g₄.wr, w₃]) (d := 248) (by omega) fun s₉ g₉ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₁₀ u₁₀ => ?_
  refine str_ok hp (by rw [u₁₀.other _ (by decide), g₉.gpr, g₈.gpr, g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, c₃])
    (by rw [u₁₀.wr, g₉.wr, g₈.wr, g₇.wr, g₆.wr, g₅.wr, g₄.wr, w₃]) (d := 252) (by omega) fun s₁₁ g₁₁ => ?_
  have G : ∀ r, r ≠ .r12 → s₁₁.gpr r = s.gpr r := fun r hr => by
    rw [g₁₁.gpr, u₁₀.other r hr, g₉.gpr, g₈.gpr, g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, u₃.other r hr, g₂.gpr,
      u₁.other r hr]
  refine k s₁₁ G (by rw [g₁₁.rd, u₁₀.rd, g₉.rd, g₈.rd, g₇.rd, g₆.rd, g₅.rd, g₄.rd, u₃.rd, g₂.rd, u₁.rd])
    (by rw [g₁₁.wr, u₁₀.wr, g₉.wr, g₈.wr, g₇.wr, g₆.wr, g₅.wr, g₄.wr, u₃.wr, g₂.wr, u₁.wr])
    (by rw [g₁₁.sp, u₁₀.sp, g₉.sp, g₈.sp, g₇.sp, g₆.sp, g₅.sp, g₄.sp, u₃.sp, g₂.sp, u₁.sp]) ?_
  have e : ∀ o : Nat, scA s₀ + BitVec.ofNat 64 (224 + o) = P + BitVec.ofNat 64 o := fun o => (add_ofNat _ _ _).symm
  have e₂ : s₂.mem = writeBytes s.mem P ([] ++ [0x80, 0, 0, 0]) := by
    rw [g₂.mem, u₁.gpr, u₁.mem, ← writeBytes_nil s.mem P]
    exact writeW_append _ _ _ _ _ (by simp [P]) (by decide) (by decide)
  have e₄ : s₄.mem = writeBytes s.mem P ([0x80, 0, 0, 0] ++ [0, 0, 0, 0]) := by
    rw [g₄.mem, z₃, u₃.mem, e₂]; exact writeW_append _ _ _ _ _ (e 4) (by decide) (by decide)
  have e₅ : s₅.mem = writeBytes s.mem P ([0x80, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0]) := by
    rw [g₅.mem, g₄.gpr, z₃, e₄]; exact writeW_append _ _ _ _ _ (e 8) (by decide) (by decide)
  have e₆ : s₆.mem = writeBytes s.mem P ([0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0]) := by
    rw [g₆.mem, g₅.gpr, g₄.gpr, z₃, e₅]; exact writeW_append _ _ _ _ _ (e 12) (by decide) (by decide)
  have e₇ : s₇.mem = writeBytes s.mem P ([0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0]) := by
    rw [g₇.mem, g₆.gpr, g₅.gpr, g₄.gpr, z₃, e₆]; exact writeW_append _ _ _ _ _ (e 16) (by decide) (by decide)
  have e₈ : s₈.mem = writeBytes s.mem P
      ([0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0]) := by
    rw [g₈.mem, g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, z₃, e₇]
    exact writeW_append _ _ _ _ _ (e 20) (by decide) (by decide)
  have e₉ : s₉.mem = writeBytes s.mem P
      ([0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0]) := by
    rw [g₉.mem, g₈.gpr, g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, z₃, e₈]
    exact writeW_append _ _ _ _ _ (e 24) (by decide) (by decide)
  rw [g₁₁.mem, u₁₀.gpr, u₁₀.mem, e₉]
  exact writeW_append _ _ _ _ _ (e 28) (by decide) (by decide)

/-! ## The prologue -/

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block prologue) s₀ (fun s => Inv s₀ (nn s₀) s ∧ s.z = decide (nn s₀ = 0)) := by
  have := hp.scr_fit; have := hp.t_fit; have := hp.u_fit
  unfold prologue
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl ⟨argR s₀, by simp [hp.rd], Region.contains_self _ _⟩
    fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = scr s₀ := u₁.gpr
  refine save_ok (b := .r12) (by rw [h12]; omega) (fun d _ hd₂ => by
    rw [h12, u₁.wr]; exact in_scr hp rfl (by omega)) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => ?_
  have G : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r h => by rw [g₂, u₁.other r h]
  have rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  have sp₆ : s₆.sp = s₀.sp := by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  have M₆ : s₆.mem = saveMem s₀.mem (scA s₀) s₁.gpr saved := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂, h12, u₁.mem]
  have r0₆ : s₆.gpr .r0 = tP s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), G _ (by decide)]
  have r1₆ : s₆.gpr .r1 = uP s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      G _ (by decide)]
  have r3₆ : s₆.gpr .r3 = scr s₀ := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, h12]
  have r4₆ : s₆.gpr .r4 = key s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, G _ (by decide)]
  have r5₆ : s₆.gpr .r5 = s₀.gpr .r2 := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), G _ (by decide)]
  have F₆ : Frame [⟨scA s₀, 160⟩] s₀.mem s₆.mem := by
    rw [M₆]; exact saveMem_frame _ _ _ saved fun p hp' => (saved_bound p hp').1
  have sc160 : ∀ r ∈ [(⟨scA s₀, 160⟩ : Region)], r ∈ [tR s₀, scR s₀] ∨ Region.Sub r (scR s₀) :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inr (Region.sub_prefix (by omega))
  -- `U` into the block.
  refine copy_ok (t := .r12) (src := .r1) (dst := .r3) (by decide) (by decide) 0 192 8 ⟨by omega, by omega⟩ _ s₆ _
    (by rw [r1₆]; omega) (by rw [r3₆]; omega)
    (fun j hj => by
      rw [r1₆, rd₆, wr₆, add_ofNat]
      exact ⟨uR s₀, by simp [hp.rd], contains_offset (by omega) (by omega)⟩)
    (fun j hj => by rw [r3₆, wr₆, add_ofNat]; exact in_scr hp rfl (by omega)) ?_
    fun s₇ g₇ rd₇ wr₇ sp₇ m₇ => ?_
  · rw [r1₆, r3₆]
    exact Region.Disjoint.sep hp.u_s (contains_offset (by omega) (by omega)) (contains_offset (by omega) (by omega))
  -- `T` into the scratch space.
  refine copy_ok (t := .r12) (src := .r0) (dst := .r3) (by decide) (by decide) 0 160 8 ⟨by omega, by omega⟩ _ s₇ _
    (by rw [g₇ _ (by decide), r0₆]; omega) (by rw [g₇ _ (by decide), r3₆]; omega)
    (fun j hj => by
      rw [g₇ _ (by decide), r0₆, rd₇, wr₇, wr₆, add_ofNat]
      exact InRegions.right (in_t hp rfl (by omega)))
    (fun j hj => by rw [g₇ _ (by decide), r3₆, wr₇, wr₆, add_ofNat]; exact in_scr hp rfl (by omega)) ?_
    fun s₈ g₈ rd₈ wr₈ sp₈ m₈ => ?_
  · rw [g₇ _ (by decide), g₇ _ (by decide), r0₆, r3₆]
    exact Region.Disjoint.sep hp.t_s (contains_offset (by omega) (by omega)) (contains_offset (by omega) (by omega))
  refine padding_ok hp (by rw [g₈ _ (by decide), g₇ _ (by decide), r3₆]) (by rw [wr₈, wr₇, wr₆])
    fun s₉ g₉ rd₉ wr₉ sp₉ m₉ => ?_
  refine wp_cmp (op2_imm (by decide)) fun s₁₀ f₁₀ z₁₀ => WP.block_nil ?_
  have G₁₀ : ∀ r, r ≠ .r12 → s₁₀.gpr r = s₆.gpr r := fun r h => by rw [f₁₀.gpr, g₉ r h, g₈ r h, g₇ r h]
  simp only [g₇ _ (show Reg.r0 ≠ .r12 by decide), g₇ _ (show Reg.r3 ≠ .r12 by decide), r1₆, r0₆, r3₆,
    ofNat_zero] at m₇ m₈
  rw [show 4 * 8 = 32 from rfl] at m₇ m₈
  have hm : s₁₀.mem = writeBytes (writeBytes (writeBytes s₆.mem (blkA s₀) (bytesAt s₆.mem (uA s₀) 32))
      (TA s₀) (bytesAt s₇.mem (tA s₀) 32)) (scA s₀ + BitVec.ofNat 64 224) pad96 := by
    rw [f₁₀.mem, m₉, m₈, m₇]
  have fU : Frame [sR s₀ 192 32, sR s₀ 160 32, sR s₀ 224 32] s₆.mem s₁₀.mem := by
    rw [hm]
    exact (((writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact contains_base (Nat.le_refl _))).mono (by simp)).trans
      ((writeBytes_frame _ _ _ (R := sR s₀ 160 32) (by rw [bytesAt_length]; exact contains_base (Nat.le_refl _))).mono
        (by simp))).trans
      ((writeBytes_frame _ _ _ (R := sR s₀ 224 32) (contains_base (by decide))).mono (by simp))
  have F' : Frame [scR s₀] s₀.mem s₁₀.mem :=
    (F₆.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩).trans
    (fU.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨scR s₀, by simp, scr_sub s₀ (by omega)⟩)
  have s160 : Region.Sub ⟨scA s₀, 160⟩ (scR s₀) := Region.sub_prefix (by omega)
  have hU₆ : bytesAt s₆.mem (uA s₀) 32 = bytesAt s₀.mem (uA s₀) 32 :=
    frame_bytesAt F₆ (by simpa using hp.u_s.sub_right s160) (by omega)
  have hT₇ : bytesAt s₇.mem (tA s₀) 32 = bytesAt s₀.mem (tA s₀) 32 := by
    rw [m₇, bytesAt_writeBytes_sep _ _ (Region.Disjoint.sep (hp.t_s.sub_right (scr_sub s₀ (o := 192) (n := 32)
      (by omega))) (contains_base (Nat.le_refl _)) (by rw [bytesAt_length]; exact contains_base (Nat.le_refl _))) (by omega)]
    exact frame_bytesAt F₆ (by simpa using hp.t_s.sub_right s160) (by omega)
  have sep : ∀ {a b : Nat}, a + 32 ≤ b ∨ b + 32 ≤ a → a + 32 ≤ 384 → b + 32 ≤ 384 → ∀ xs : List Byte,
      xs.length = 32 → Mem.Sep (scA s₀ + BitVec.ofNat 64 a) 32 (scA s₀ + BitVec.ofNat 64 b) xs.length :=
    fun h ha hb xs hx => Region.Disjoint.sep (scr_disj s₀ h ha hb) (contains_base (Nat.le_refl _))
      (by rw [hx]; exact contains_base (Nat.le_refl _))
  have hB : bytesAt s₁₀.mem (blkA s₀) 32 = bytesAt s₀.mem (uA s₀) 32 := by
    rw [hm, bytesAt_writeBytes_sep _ _ (sep (a := 192) (b := 224) (by omega) (by omega) (by omega) _ rfl) (by omega),
      bytesAt_writeBytes_sep _ _ (sep (a := 192) (b := 160) (by omega) (by omega) (by omega) _ (bytesAt_length _ _ _))
        (by omega)]
    have := bytesAt_writeBytes_self s₆.mem (blkA s₀) (bytesAt s₆.mem (uA s₀) 32) (by rw [bytesAt_length]; omega)
    rw [bytesAt_length] at this
    rw [this, hU₆]
  have hT : bytesAt s₁₀.mem (TA s₀) 32 = bytesAt s₀.mem (tA s₀) 32 := by
    rw [hm, bytesAt_writeBytes_sep _ _ (sep (a := 160) (b := 224) (by omega) (by omega) (by omega) _ rfl) (by omega)]
    have := bytesAt_writeBytes_self (writeBytes s₆.mem (blkA s₀) (bytesAt s₆.mem (uA s₀) 32)) (TA s₀)
      (bytesAt s₇.mem (tA s₀) 32) (by rw [bytesAt_length]; omega)
    rw [bytesAt_length] at this
    rw [this, hT₇]
  have hS : ∀ p ∈ saved, s₁₀.mem.readW (scA s₀ + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1 := by
    intro p hp'
    have hb := saved_bound p hp'
    rw [fU.readW (r := sR s₀ p.2 4) (Region.contains_self _ _) ?_ (by decide), M₆,
      saveMem_saved _ _ _ p hp', u₁.other]
    · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact scr_disj s₀ (by omega) (by omega) (by omega)
  refine ⟨⟨⟨by rw [f₁₀.rd, rd₉, rd₈, rd₇, rd₆], by rw [f₁₀.wr, wr₉, wr₈, wr₇, wr₆],
    by rw [f₁₀.sp, sp₉, sp₈, sp₇, sp₆], by rw [G₁₀ _ (by decide), r0₆], by rw [G₁₀ _ (by decide), r3₆],
    by rw [G₁₀ _ (by decide), r4₆], F'.mono (by simp)⟩, by rw [G₁₀ _ (by decide), r5₆, ofNat_toNat32], hS, ?_,
    (Nat.le_refl _), by rw [hB, hT]⟩, ?_⟩
  · rw [hm]
    exact bytesAt_writeBytes_self _ (scA s₀ + BitVec.ofNat 64 224) pad96 (by decide)
  · rw [z₁₀, g₉ _ (by decide), g₈ _ (by decide), g₇ _ (by decide), r5₆, beq_zero_toNat]

/-! ## The epilogue -/

/-- The postcondition. -/
def Post (s₀ s' : State) : Prop := abiPreserved s₀ s' ∧ Proof.Pbkdf2.iterateSha256Arm.post s₀ s'

/-- With the key's streaming states as the contract requires, a step is HMAC-SHA-256. -/
theorem stepM_eq {s₀ : State} {k0 : List Byte} (hk : k0.length = 64)
    (hi : Repr s₀.mem (kA s₀) (xorPad k0 ipad)) (ho : Repr s₀.mem (kA s₀ + 96) (xorPad k0 opad))
    {u : List Byte} (hu : u.length = 32) :
    hmacBlockKey sha256 k0 u = stepM s₀ u := by
  have li : (xorPad k0 ipad).length = 64 := by simp [xorPad, hk]
  have lo : (xorPad k0 opad).length = 64 := by simp [xorPad, hk]
  have ho1 : stateAt s₀.mem (kA s₀ + BitVec.ofNat 64 96) = _ := ho.1
  rw [hmac_step hk hu, stepM, Hi, Ho, ofNat_zero, hi.1, ho1, li, lo]

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv s₀ 0 s) :
    WP isa (.block epilogue) s (Post s₀) := by
  have := hp.scr_fit; have := hp.t_fit
  unfold epilogue
  refine copy_ok (t := .r12) (src := .r3) (dst := .r0) (by decide) (by decide) 160 0 8 ⟨by omega, by omega⟩ _ s _
    (by rw [h.r3]; omega) (by rw [h.r0]; omega)
    (fun j hj => by rw [h.r3, add_ofNat]; exact InRegions.right (in_scr hp h.wr (by omega)))
    (fun j hj => by rw [h.r0, add_ofNat]; exact in_t hp h.wr (by omega)) ?_ fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  · rw [h.r3, h.r0]
    exact Region.Disjoint.sep hp.t_s.symm (contains_offset (by omega) (by omega)) (contains_offset (by omega) (by omega))
  simp only [h.r3, h.r0, ofNat_zero] at m₁
  rw [show 4 * 8 = 32 from rfl] at m₁
  have fT : Frame [tR s₀] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact contains_base (Nat.le_refl _))
  refine restore_ok (scr := scr s₀) (by rw [g₁ _ (by decide), h.r3]) (by omega)
    (fun d _ hd₂ => by rw [rd₁, wr₁]; exact InRegions.right (in_scr hp h.wr (by omega))) s₀.gpr
    (fun p hp' => ?_) fun s' hs _ hmem _ _ hsp => ⟨⟨fun r hr => ?_, by rw [hsp, sp₁, h.sp]⟩, fun k0 hk hi ho => ?_⟩
  · rw [← h.saved p hp']
    have hb := saved_bound p hp'
    exact fT.readW (r := sR s₀ p.2 4) (Region.contains_self _ _)
      (by simpa using (hp.t_s.sub_right (scr_sub s₀ (o := p.2) (n := 4) (by omega))).symm) (by decide)
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hs (.r4, 112) (by simp [saved])
    · exact hs (.r5, 116) (by simp [saved])
    · exact hs (.r6, 120) (by simp [saved])
    · exact hs (.r7, 124) (by simp [saved])
    · exact hs (.r8, 128) (by simp [saved])
    · exact hs (.r9, 132) (by simp [saved])
    · exact hs (.r10, 136) (by simp [saved])
    · exact hs (.r11, 140) (by simp [saved])
    · exact hs (.lr, 144) (by simp [saved])
  · have := h.val
    simp only [Spec.Pbkdf2.iterate] at this
    have e : bytesAt s'.mem (tA s₀) 32 = bytesAt s.mem (TA s₀) 32 := by
      have := bytesAt_writeBytes_self s.mem (tA s₀) (bytesAt s.mem (TA s₀) 32) (by rw [bytesAt_length]; omega)
      rw [bytesAt_length] at this
      rw [hmem, m₁, this]
    show bytesAt s'.mem (tA s₀) 32 = _
    rw [e, ← this]
    exact (iterate_congr (fun u hu => stepM_eq hk hi ho hu) (fun u => Pbkdf2.digest_length _) _ _ _
      (bytesAt_length _ _ _)).symm

/-! ## Correctness -/

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa iterate s₀ (Post s₀) := by
  unfold iterate
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨h₁, z₁⟩ => ?_)
  exact WP.seq (WP.mono (loop_ok hp h₁ z₁) fun s₂ h₂ => epilogue_ok hp h₂)

/-! ## `Verified` -/

/-- The initial taint: `r0`–`r3` (`key`, `u`, `n`, `t`) are public, `r3`
points at `t`, and the 4 bytes of stack arguments are public, pointing at
the scratch space. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [32, 384], bases := [(.r3, 0)],
    argLen := 4, argBases := [(0, 1)] }

theorem wf₀ {s : State} (h : Proof.Pbkdf2.iterateSha256Arm.pre s) : VG.Arm.Taint.Wf τ₀ s := by
  have hp := pre_of h
  have ht := hp.t_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩, ?_, fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨hp.t_s, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega
  · intro p hp'
    simp only [τ₀, List.mem_singleton] at hp'
    subst hp'; simp [VG.Arm.Taint.region, hp.wr]
  · have e : (⟨State.addr s.sp, 4⟩ : Region) = argR s := by simp [stackArgAddr]
    simp only [τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.a_t
    · exact hp.a_s
  · intro p hp'; simp only [τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem argByte_eq (s : State) (k : Nat) :
    VG.Arm.Taint.argByte s k = stackArgAddr s 0 + BitVec.ofNat 64 k := by
  simp [VG.Arm.Taint.argByte, stackArgAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Pbkdf2.iterateSha256Arm.pre s₁)
    (h₂ : Proof.Pbkdf2.iterateSha256Arm.pre s₂) (hpub : Proof.Pbkdf2.iterateSha256Arm.pub s₁ s₂) :
    VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp, fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [tR, scR, tA, scA, tP, scr, p3, a0]
  · simp only [τ₀] at hk
    rw [argByte_eq, argByte_eq, Mem.readW_byte s₁.mem _ hk, Mem.readW_byte s₂.mem _ hk]
    exact congrArg _ a0

/-- A state satisfying the precondition: `key` at `0x1000`, `u` at `0x2000`,
`t` at `0x3000` and the scratch space at `0x4000`, passed on the stack at
`0x5000`. -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x5001 then 0x40 else 0
  rd := [⟨0x1000, 192⟩, ⟨0x2000, 32⟩, ⟨0x5000, 4⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 384⟩]

theorem iterate_correct (s : State) (hs : Proof.Pbkdf2.iterateSha256Arm.pre s) :
    ∃ t s', Exec isa iterate s t s' ∧ abiPreserved s s' ∧ Proof.Pbkdf2.iterateSha256Arm.post s s' :=
      by
  obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
  exact ⟨t, s', he, h⟩

theorem iterate_ct : ConstantTime isa Proof.Pbkdf2.iterateSha256Arm.pre
    Proof.Pbkdf2.iterateSha256Arm.pub iterate := by
  exact VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
    (by taint_decide)

/-- `iterateSha256Arm` with the 832 bytes of scratch of the shared contract
(sized for the x86-64 AVX2 compression function), of which the code uses 384. -/
def iterateWide : Contract isa :=
  { Proof.Pbkdf2.iterateSha256Arm with
    pre := fun s =>
      let key : Region := ⟨State.addr (s.gpr .r0), 192⟩
      let u : Region := ⟨State.addr (s.gpr .r1), 32⟩
      let t : Region := ⟨State.addr (s.gpr .r3), 32⟩
      let scratch : Region := ⟨State.addr (stackArg s 0), 832⟩
      let args : Region := ⟨stackArgAddr s 0, 4⟩
      s.rd = [key, u, args] ∧ s.wr = [t, scratch] ∧
      key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧
      t.Disjoint scratch ∧ args.Disjoint t ∧ args.Disjoint scratch ∧
      (s.gpr .r0).toNat + 192 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 32 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 832 ≤ 2 ^ 32 ∧
      s.sp.toNat + 4 ≤ 2 ^ 32 }

/-- The regions `iterateSha256Arm` lets the code write. -/
def narrowWr (s : State) : List Region :=
  [⟨State.addr (s.gpr .r3), 32⟩, ⟨State.addr (stackArg s 0), 384⟩]

/-- Rewrites the contracts at a narrowed state (`stackArg` does not unfold
cheaply). -/
local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Pbkdf2.iterateSha256Arm, VG.Proof.Pbkdf2.Arm.iterateWide, VG.Proof.Pbkdf2.Arm.narrowWr, VG.Arm.stackArg_withRegions, VG.Arm.stackArgAddr_withRegions,
    VG.Arm.State.withRegions_gpr, VG.Arm.State.withRegions_sp, VG.Arm.State.withRegions_mem,
    VG.Arm.State.withRegions_rd, VG.Arm.State.withRegions_wr] $(loc)?)

theorem iterateWide_pre (s : State) (h : iterateWide.pre s) :
    Proof.Pbkdf2.iterateSha256Arm.pre (s.withRegions s.rd (narrowWr s)) := by
  obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄⟩ := h
  narrow
  exact ⟨h₁, trivial, h₃, h₄.sub_right (Region.sub_of_ble rfl), h₅,
    h₆.sub_right (Region.sub_of_ble rfl), h₇.sub_right (Region.sub_of_ble rfl), h₈,
    h₉.sub_right (Region.sub_of_ble rfl), h₁₀, h₁₁, h₁₂, Region.end_le_of_ble rfl h₁₃, h₁₄⟩

/-- A state satisfying `iterateWide.pre`. -/
def wideSat : State := { sat with wr := [⟨0x3000, 32⟩, ⟨0x4000, 832⟩] }

theorem iterateWide_implies : iterateWide.Implies (Spec.Pbkdf2.iterateSha256Contract Arm.abi) := by
  sig_implies [Spec.Pbkdf2.iterateSha256Contract, Spec.Pbkdf2.iterateSha256Sig, iterateWide,
    Proof.Pbkdf2.iterateSha256Arm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [wideSat, sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using wideSat

/-- The proof is written against `iterateSha256Arm`, widened to the shared
contract's scratch. -/
theorem iterate_verified :
    Verified Arm.target Impl.Pbkdf2.Arm.iterate (Spec.Pbkdf2.iterateSha256Contract Arm.abi) :=
  have hsat := iterateWide_implies.sat_left
  (Verified.widen (Verified.of_correct iterate_correct iterate_ct
    (.refl (hsat.elim fun s hs => ⟨_, iterateWide_pre s hs⟩)))
    narrowWr iterateWide_pre
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (Region.prefix_of_ble rfl) (.cons (Region.prefix_of_ble rfl) .nil))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat).of_implies iterateWide_implies

end VG.Proof.Pbkdf2.Arm
