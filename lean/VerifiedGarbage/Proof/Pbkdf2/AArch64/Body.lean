import VerifiedGarbage.Proof.Pbkdf2.AArch64.Common

/-!
# PBKDF2-HMAC-SHA-256's iteration on AArch64: the loop

Untrusted: everything here is checked by Lean. One step is HMAC-SHA-256 of
`U` as two compressions (`VG.Proof.Pbkdf2.hmac_step`), then `T ← T ⊕ U`.
-/

namespace VG.Proof.Pbkdf2.AArch64

open VG VG.AArch64 VG.Impl.Pbkdf2.AArch64
open VG.Impl.Sha256.AArch64.Stream (saved)
open VG.Proof.Hmac.X86_64 (bytesAt_length bytesAt_writeBytes_self bytesAt_writeBytes_sep)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.MdStream.AArch64 (wp_subImm eval_zero eval_nonzero ofNat_beq_zero ofNat_pred)
open VG.Proof.Pbkdf2.X86_64.Iterate (frame_bytesAt contains_base blockAt_eq xorBytes_length add_ofNat digest_self)
open VG.Spec.Sha256 (bytesAt stateAt blockAt compress HashValue)

section
variable (s₀ : State)

/-- The key's inner and outer hash values. -/
abbrev Hi : HashValue := stateAt s₀.mem (key s₀ + BitVec.ofNat 64 0)
abbrev Ho : HashValue := stateAt s₀.mem (key s₀ + BitVec.ofNat 64 96)

/-- A step, as the code computes it. -/
def stepM (u : List Byte) : List Byte :=
  Pbkdf2.digest (compress (Ho s₀) (block96 (Pbkdf2.digest (compress (Hi s₀) (block96 u)))))

/-- Our caller's registers and our return address, saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  (∀ p ∈ saved, m.readW (scr s₀ + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1) ∧
  m.readW (scr s₀ + BitVec.ofNat 64 256) 64 = s₀.gpr .x30

/-- What the body writes: the compression's part of the scratch space, the
hash value being compressed, the block's first 32 bytes and `T`. -/
abbrev bodyR : List Region := [stR s₀, cmpR s₀, sR s₀ 192 32, tR s₀]

end

/-- Parts of the scratch space that the body leaves: the saved registers
(`[112..160)`), the padding and the saved return address (from 224). -/
theorem body_disj {s₀ : State} (hp : Pre s₀) {o n : Nat} (h₁ : (112 ≤ o ∧ o + n ≤ 160) ∨ 224 ≤ o)
    (h₂ : o + n ≤ 384) : ∀ r ∈ bodyR s₀, Region.Disjoint (sR s₀ o n) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact scr_disj s₀ (b := 160) (n := 32) (by omega) h₂ (by omega)
  · exact scr_disj0 s₀ (by omega) h₂
  · exact scr_disj s₀ (b := 192) (n := 32) (by omega) h₂ (by omega)
  · exact (hp.t_s.sub_right (scr_sub s₀ h₂)).symm

/-- The block's first 32 bytes are neither the hash value nor the compression's scratch. -/
theorem blk_disj (s₀ : State) : ∀ r ∈ [stR s₀, cmpR s₀], Region.Disjoint (sR s₀ 192 32) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact scr_disj s₀ (b := 160) (n := 32) (by omega) (by omega) (by omega)
  · exact scr_disj0 s₀ (by omega) (by omega)

theorem Saved.frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Saved s₀ m) (hf : Frame (bodyR s₀) m m') :
    Saved s₀ m' := by
  refine ⟨fun p hp' => ?_, ?_⟩
  · rw [← h.1 p hp']
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    have hd : 112 ≤ p.2 ∧ p.2 + 8 ≤ 160 := by rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    exact hf.readW (r := sR s₀ p.2 8) (Region.contains_self _ _) (body_disj hp (.inl hd) (by omega)) (by decide)
  · rw [← h.2]
    exact hf.readW (r := sR s₀ 256 8) (Region.contains_self _ _) (body_disj hp (.inr (by omega)) (by omega))
      (by decide)

theorem frame_body {s₀ : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hs : ∀ r ∈ rs, r ∈ bodyR s₀) :
    Frame (bodyR s₀) m m' := hf.mono hs

/-- The loop invariant, with `r` steps left. -/
structure Inv (s₀ : State) (r : Nat) (s : State) : Prop extends Regs s₀ s where
  x23 : s.gpr .x23 = BitVec.ofNat 64 r
  saved : Saved s₀ s.mem
  pad : bytesAt s.mem (scr s₀ + BitVec.ofNat 64 224) 32 = pad96
  le : r ≤ nn s₀
  val : Spec.Pbkdf2.iterate (stepM s₀) (nn s₀) (bytesAt s₀.mem (uP s₀) 32) (bytesAt s₀.mem (tP s₀) 32) =
    Spec.Pbkdf2.iterate (stepM s₀) r (bytesAt s.mem (blkA s₀) 32) (bytesAt s.mem (tP s₀) 32)

theorem body_ok {s₀ : State} (hp : Pre s₀) {r : Nat} {s : State} (h : Inv s₀ (r + 1) s) :
    WP isa body s fun s' => eval (.nonzero .x .x23) s' = some (r != 0) ∧ Inv s₀ r s' := by
  unfold body
  have hU : ∀ {m : Mem}, Frame [stR s₀, cmpR s₀] s.mem m → bytesAt m (blkA s₀) 32 = bytesAt s.mem (blkA s₀) 32 :=
    fun hf => frame_bytesAt hf (blk_disj s₀) (by omega)
  have hpad : ∀ {m : Mem}, Frame (bodyR s₀) s.mem m → bytesAt m (blkA s₀ + 32) 32 = pad96 := by
    intro m hf
    rw [show blkA s₀ + 32 = scr s₀ + BitVec.ofNat 64 224 by bv_omega, ← h.pad]
    exact frame_bytesAt hf (body_disj hp (o := 224) (n := 32) (.inr (Nat.le_refl _)) (by omega)) (by omega)
  -- The inner hash.
  refine WP.seq ?_
  refine load_ok hp h.toRegs (o := 0) (by omega) (by decide) fun s₁ k₁ e₁ => ?_
  refine atBlock_ok (h.toRegs.keep k₁) fun s₂ k₂ m₂ x1₂ => ?_
  have h₂ := (h.toRegs.keep k₁).keep k₂
  refine WP.seq (cmp_ok hp h₂ x1₂ fun s₃ k₃ e₃ => ?_)
  rw [m₂, e₁, blockAt_eq (hpad (frame_body k₁.frame (by simp))), hU k₁.frame] at e₃
  -- The outer hash.
  have h₃ := h₂.keep k₃
  refine WP.seq ?_
  refine digest_ok hp h₃ fun s₄ h₄ g₄ f₄ m₄ => ?_
  refine load_ok hp h₄ (o := 96) (by omega) (by decide) fun s₅ k₅ e₅ => ?_
  refine atBlock_ok (h₄.keep k₅) fun s₆ k₆ m₆ x1₆ => ?_
  have h₆ := (h₄.keep k₅).keep k₆
  have f₃₄ : Frame (bodyR s₀) s.mem s₄.mem :=
    (frame_body ((k₁.trans k₂).trans k₃).frame (by simp)).trans (frame_body f₄ (by simp))
  refine WP.seq (cmp_ok hp h₆ x1₆ fun s₇ k₇ e₇ => ?_)
  have hX : bytesAt s₅.mem (blkA s₀) 32 = Pbkdf2.digest (stateAt s₃.mem (stA s₀)) := by
    rw [frame_bytesAt (p := blkA s₀) (n := 32) k₅.frame (blk_disj s₀) (by omega), m₄, digest_self]
  rw [m₆, e₅, blockAt_eq (hpad (f₃₄.trans (frame_body k₅.frame (by simp)))), hX, e₃] at e₇
  -- The digest, `T ← T ⊕ U` and the count.
  have h₇ := h₆.keep k₇
  refine digest_ok hp h₇ fun s₈ h₈ g₈ f₈ m₈ => ?_
  have hd : Region.Disjoint (tR s₀) ⟨scr s₀ + BitVec.ofNat 64 192, 32⟩ :=
    hp.t_s.sub_right (scr_sub s₀ (o := 192) (by omega))
  refine xor_ok (tp := tP s₀) (sc := scr s₀) hd 4 (Nat.le_refl _) _ s₈ _ h₈.x22 h₈.x20
    (fun j hj => InRegions.right (by rw [add_ofNat]; exact in_scr hp h₈.wr (a := 192 + 8 * j) (n := 8) (by omega)))
    (fun j hj => in_t hp h₈.wr (b := 8 * j) (n := 8) (by omega)) fun s₉ g₉ rd₉ wr₉ sp₉ m₉ => ?_
  rw [show 8 * 4 = 32 from rfl] at m₉
  have f₉ : Frame [tR s₀] s₈.mem s₉.mem := by
    rw [m₉]; exact writeBytes_frame _ _ _ (contains_base (by rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]))
  have h₉ := h₈.write (fun r hr => g₉ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) rd₉ wr₉ sp₉ (R := tR s₀) (by simp) f₉
  refine wp_subImm (by omega) fun s₁₀ u₁₀ => WP.block_nil ?_
  have h₁₀ := h₉.write (fun r hr => u₁₀.other r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) u₁₀.rd u₁₀.wr u₁₀.sp (R := tR s₀) (by simp)
    (by rw [u₁₀.mem]; exact Frame.refl _ _)
  have x23 : s₉.gpr .x23 = BitVec.ofNat 64 (r + 1) := by
    rw [g₉ _ (by decide) (by decide), g₈ _ (by decide), k₇.gpr _ (by simp [kept]), k₆.gpr _ (by simp [kept]),
      k₅.gpr _ (by simp [kept]), g₄ _ (by decide), k₃.gpr _ (by simp [kept]), k₂.gpr _ (by simp [kept]),
      k₁.gpr _ (by simp [kept]), h.x23]
  have hlt : r + 1 < 2 ^ 64 := by have := h.le; have := hp.n32; omega
  have e₁₀ : s₉.gpr .x23 - BitVec.ofNat 64 1 = BitVec.ofNat 64 r := by
    rw [x23, show BitVec.ofNat 64 1 = 1 from rfl, ofNat_pred (by omega)]; rfl
  have fb : Frame (bodyR s₀) s.mem s₁₀.mem := by
    rw [u₁₀.mem]
    exact f₃₄.trans (frame_body ((k₅.trans k₆).trans k₇).frame (by simp)) |>.trans (frame_body f₈ (by simp))
      |>.trans (frame_body f₉ (by simp))
  have f₈' : Frame [stR s₀, cmpR s₀, sR s₀ 192 32] s.mem s₈.mem :=
    (((k₁.trans k₂).trans k₃).frame.mono (by simp)) |>.trans (f₄.mono (by simp))
      |>.trans ((((k₅.trans k₆).trans k₇).frame).mono (by simp)) |>.trans (f₈.mono (by simp))
  have hT : bytesAt s₈.mem (tP s₀) 32 = bytesAt s.mem (tP s₀) 32 := by
    refine frame_bytesAt f₈' (fun r hr => ?_) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.t_s.sub_right (scr_sub s₀ (o := 160) (by omega))
    · exact hp.t_s.sub_right (cmp_sub s₀)
    · exact hd
  have hU₈ : bytesAt s₈.mem (blkA s₀) 32 = stepM s₀ (bytesAt s.mem (blkA s₀) 32) := by
    rw [m₈, digest_self, e₇]; rfl
  have hU₁₀ : bytesAt s₁₀.mem (blkA s₀) 32 = stepM s₀ (bytesAt s.mem (blkA s₀) 32) := by
    rw [u₁₀.mem, m₉, bytesAt_writeBytes_sep _ _ (fun x h₁ h₂ => hd x ?_ ?_) (by omega), hU₈]
    · simp only [Region.Contains]; rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length] at h₂; omega
    · simp only [Region.Contains, blkA] at h₁ ⊢; omega
  have hT₁₀ : bytesAt s₁₀.mem (tP s₀) 32 =
      Spec.Pbkdf2.xorBytes (bytesAt s.mem (tP s₀) 32) (stepM s₀ (bytesAt s.mem (blkA s₀) 32)) := by
    have := bytesAt_writeBytes_self s₈.mem (tP s₀)
      (Spec.Pbkdf2.xorBytes (bytesAt s₈.mem (tP s₀) 32) (bytesAt s₈.mem (scr s₀ + BitVec.ofNat 64 192) 32))
      (by rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
    rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length] at this
    rw [u₁₀.mem, m₉, this, hT, hU₈]
  have hle : r ≤ nn s₀ := by have := h.le; omega
  refine ⟨?_, { h₁₀ with x23 := ?_, saved := h.saved.frame hp fb, pad := ?_, le := hle, val := ?_ }⟩
  · rw [eval_nonzero, u₁₀.gpr, e₁₀]
    simp only [bne, ofNat_beq_zero (by omega : r < 2 ^ 64)]
    cases r <;> rfl
  · rw [u₁₀.gpr, e₁₀]
  · rw [← h.pad]
    exact frame_bytesAt fb (body_disj hp (o := 224) (n := 32) (.inr (Nat.le_refl _)) (by omega)) (by omega)
  · rw [h.val, hU₁₀, hT₁₀]; rfl

theorem loop_ok {s₀ : State} (hp : Pre s₀) {n : Nat} {s : State} (h : Inv s₀ n s) :
    WP isa (.ite (.zero .x .x23) (.block []) (.loop body (.nonzero .x .x23))) s (Inv s₀ 0) := by
  have hn : n < 2 ^ 64 := by have := h.le; have := hp.n32; omega
  refine WP.ite (decide (n = 0))
    (by show VG.AArch64.eval (.zero .x .x23) s = _
        rw [eval_zero, h.x23, ofNat_beq_zero hn]) (fun hb => ?_) (fun hb => ?_)
  · obtain rfl : n = 0 := by simpa using hb
    exact WP.block_nil h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hb; omega⟩
    refine WP.loop (fun m s => Inv s₀ (m + 1) s) (fun m s hs => WP.mono (body_ok hp hs) fun s' ⟨he, hi⟩ => ?_) m s h
    cases m with
    | zero => exact .inl ⟨he, hi⟩
    | succ m => exact .inr ⟨he, m, by omega, hi⟩

end VG.Proof.Pbkdf2.AArch64
