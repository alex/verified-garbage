import VerifiedGarbage.Proof.Pbkdf2.X86.Common

/-!
# PBKDF2-HMAC-SHA-256's iteration on x86 (32-bit): the loop

Untrusted: everything here is checked by Lean. One step is HMAC-SHA-256 of
`U` as two compressions (`VG.Proof.Pbkdf2.hmac_step`), then `T ← T ⊕ U`.
-/

namespace VG.Proof.Pbkdf2.X86

open VG VG.X86 VG.Impl.Pbkdf2.X86
open VG.Impl.Sha256.X86.Stream (saved)
open VG.Proof.Sha256.X86.Stream (wp_subi eval_e eval_ne ofNat_beq_zero sub_ofNat)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_writeBytes_self bytesAt_writeBytes_sep)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.Pbkdf2.Memory (frame_bytesAt contains_base blockAt_eq xorBytes_length add_ofNat digest_self)
open VG.Spec.Sha256 (bytesAt stateAt blockAt compress HashValue)

section
variable (s₀ : State)

/-- The key's inner and outer hash values. -/
abbrev Hi : HashValue := stateAt s₀.mem (kA s₀ + BitVec.ofNat 64 0)
abbrev Ho : HashValue := stateAt s₀.mem (kA s₀ + BitVec.ofNat 64 96)

/-- A step, as the code computes it. -/
def stepM (u : List Byte) : List Byte :=
  Pbkdf2.digest (compress (Ho s₀) (block96 (Pbkdf2.digest (compress (Hi s₀) (block96 u)))))

/-- Our caller's registers, saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ saved, m.readW (scA s₀ + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

/-- What the body writes: `t`, the compression's part of the scratch space,
the stack below `esp`, `T` and the block's first 32 bytes. -/
abbrev bodyR : List Region := [tR s₀, cmpR s₀, stkR s₀, sR s₀ 160 32, sR s₀ 192 32]

end

/-- Parts of the scratch space that the body leaves: the saved registers
(`[112..128)`) and the padding (from 224). -/
theorem body_disj {s₀ : State} (hp : Pre s₀) {o n : Nat} (h₁ : (112 ≤ o ∧ o + n ≤ 128) ∨ 224 ≤ o)
    (h₂ : o + n ≤ 256) : ∀ r ∈ bodyR s₀, Region.Disjoint (sR s₀ o n) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (hp.t_s.sub_right (scr_sub s₀ h₂)).symm
  · exact scr_disj0 s₀ (by omega) h₂
  · exact (hp.stk_s.sub_right (scr_sub s₀ h₂)).symm
  · exact scr_disj s₀ (b := 160) (n := 32) (by omega) h₂ (by omega)
  · exact scr_disj s₀ (b := 192) (n := 32) (by omega) h₂ (by omega)

/-- The block's first 32 bytes are neither `t`, the compression's scratch
nor the stack. -/
theorem blk_disj {s₀ : State} (hp : Pre s₀) :
    ∀ r ∈ [tR s₀, cmpR s₀, stkR s₀], Region.Disjoint (sR s₀ 192 32) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.t_s.sub_right (scr_sub s₀ (by omega))).symm
  · exact scr_disj0 s₀ (by omega) (by omega)
  · exact (hp.stk_s.sub_right (scr_sub s₀ (by omega))).symm

/-- `T` is none of the other parts the body writes. -/
theorem T_disj {s₀ : State} (hp : Pre s₀) :
    ∀ r ∈ [tR s₀, cmpR s₀, stkR s₀, sR s₀ 192 32], Region.Disjoint (sR s₀ 160 32) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hp.t_s.sub_right (scr_sub s₀ (by omega))).symm
  · exact scr_disj0 s₀ (by omega) (by omega)
  · exact (hp.stk_s.sub_right (scr_sub s₀ (by omega))).symm
  · exact scr_disj s₀ (by omega) (by omega) (by omega)

theorem saved_off {p : Reg × Nat} (hp : p ∈ saved) : 112 ≤ p.2 ∧ p.2 + 4 ≤ 128 := by
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp

theorem Saved.frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Saved s₀ m) (hf : Frame (bodyR s₀) m m') :
    Saved s₀ m' := by
  intro p hp'
  rw [← h p hp']
  have hd := saved_off hp'
  exact hf.readW (r := sR s₀ p.2 4) (Region.contains_self _ _) (body_disj hp (.inl hd) (by omega)) (by decide)

theorem frame_body {s₀ : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hs : ∀ r ∈ rs, r ∈ bodyR s₀) :
    Frame (bodyR s₀) m m' := hf.mono hs

/-- The loop invariant, with `r` steps left. -/
structure Inv (s₀ : State) (r : Nat) (s : State) : Prop extends Regs s₀ s where
  edi : s.gpr .edi = BitVec.ofNat 32 r
  saved : Saved s₀ s.mem
  pad : bytesAt s.mem (scA s₀ + BitVec.ofNat 64 224) 32 = pad96
  le : r ≤ nn s₀
  val : Spec.Pbkdf2.iterate (stepM s₀) (nn s₀) (bytesAt s₀.mem (uA s₀) 32) (bytesAt s₀.mem (tA s₀) 32) =
    Spec.Pbkdf2.iterate (stepM s₀) r (bytesAt s.mem (blkA s₀) 32) (bytesAt s.mem (TA s₀) 32)

theorem body_ok {s₀ : State} (hp : Pre s₀) {r : Nat} {s : State} (h : Inv s₀ (r + 1) s) :
    WP isa body s fun s' => VG.X86.eval .ne s' = some (r != 0) ∧ Inv s₀ r s' := by
  have := hp.scr_fit
  unfold body
  have hU : ∀ {m : Mem}, Frame [tR s₀, cmpR s₀, stkR s₀] s.mem m →
      bytesAt m (blkA s₀) 32 = bytesAt s.mem (blkA s₀) 32 :=
    fun hf => frame_bytesAt hf (blk_disj hp) (by omega)
  have hpad : ∀ {m : Mem}, Frame (bodyR s₀) s.mem m → bytesAt m (blkA s₀ + 32) 32 = pad96 := by
    intro m hf
    rw [show blkA s₀ + 32 = scA s₀ + BitVec.ofNat 64 224 by bv_omega, ← h.pad]
    exact frame_bytesAt hf (body_disj hp (o := 224) (n := 32) (.inr (Nat.le_refl _)) (by omega)) (by omega)
  -- The inner hash.
  refine WP.seq ?_
  refine load_ok hp h.toRegs (o := 0) (by omega) fun s₁ k₁ e₁ => ?_
  refine atBlock_ok (rest := []) (h.toRegs.keep k₁) fun s₂ k₂ m₂ x₂ => WP.block_nil ?_
  have h₂ := (h.toRegs.keep k₁).keep k₂
  refine WP.seq (cmp_ok hp h₂ x₂ fun s₃ k₃ e₃ => ?_)
  rw [m₂, e₁, blockAt_eq (hpad (frame_body k₁.frame (by simp))), hU k₁.frame] at e₃
  -- The outer hash.
  have h₃ := h₂.keep k₃
  refine WP.seq ?_
  refine digest_ok hp h₃ fun s₄ h₄ g₄ f₄ m₄ => ?_
  refine load_ok hp h₄ (o := 96) (by omega) fun s₅ k₅ e₅ => ?_
  refine atBlock_ok (rest := []) (h₄.keep k₅) fun s₆ k₆ m₆ x₆ => WP.block_nil ?_
  have h₆ := (h₄.keep k₅).keep k₆
  have f₃₄ : Frame (bodyR s₀) s.mem s₄.mem :=
    (frame_body ((k₁.trans k₂).trans k₃).frame (by simp)).trans (frame_body f₄ (by simp))
  refine WP.seq (cmp_ok hp h₆ x₆ fun s₇ k₇ e₇ => ?_)
  have hX : bytesAt s₅.mem (blkA s₀) 32 = Pbkdf2.digest (stateAt s₃.mem (tA s₀)) := by
    rw [frame_bytesAt (p := blkA s₀) (n := 32) k₅.frame (blk_disj hp) (by omega), m₄, digest_self]
  rw [m₆, e₅, blockAt_eq (hpad (f₃₄.trans (frame_body k₅.frame (by simp)))), hX, e₃] at e₇
  -- The digest, `T ← T ⊕ U` and the count.
  have h₇ := h₆.keep k₇
  refine digest_ok hp h₇ fun s₈ h₈ g₈ f₈ m₈ => ?_
  refine xor_ok (p := scr s₀) (by omega) 8 (Nat.le_refl _) _ s₈ _ h₈.ebp
    (fun j hj => InRegions.right (by rw [add_ofNat]; exact in_scr hp h₈.wr (a := 192 + 4 * j) (n := 4) (by omega)))
    (fun j hj => by rw [add_ofNat]; exact in_scr hp h₈.wr (a := 160 + 4 * j) (n := 4) (by omega))
    fun s₉ g₉ rd₉ wr₉ m₉ => ?_
  rw [show 4 * 8 = 32 from rfl] at m₉
  have f₉ : Frame [sR s₀ 160 32] s₈.mem s₉.mem := by
    rw [m₉]
    exact writeBytes_frame _ _ _ (contains_base (by rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]))
  have h₉ := h₈.write (fun r hr => g₉ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) rd₉ wr₉ (R := scR s₀) (by simp)
    (f₉.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact ⟨scR s₀, by simp, scr_sub s₀ (by omega)⟩)
  refine wp_subi fun s₁₀ u₁₀ z₁₀ => WP.block_nil ?_
  have h₁₀ := h₉.write (fun r hr => u₁₀.other r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) u₁₀.rd u₁₀.wr (R := tR s₀) (by simp)
    (by rw [u₁₀.mem]; exact Frame.refl _ _)
  have xedi : s₉.gpr .edi = BitVec.ofNat 32 (r + 1) := by
    rw [g₉ _ (by decide), g₈ _ (by decide), k₇.gpr _ (by simp [kept]), k₆.gpr _ (by simp [kept]),
      k₅.gpr _ (by simp [kept]), g₄ _ (by decide), k₃.gpr _ (by simp [kept]), k₂.gpr _ (by simp [kept]),
      k₁.gpr _ (by simp [kept]), h.edi]
  have hlt : r + 1 < 2 ^ 32 := by have := h.le; have := (arg s₀ 2).isLt; simp only [nn] at *; omega
  have e₁₀ : s₉.gpr .edi - 1 = BitVec.ofNat 32 r := by
    rw [xedi, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.add_sub_cancel]
  have fb : Frame (bodyR s₀) s.mem s₁₀.mem := by
    rw [u₁₀.mem]
    exact f₃₄.trans (frame_body ((k₅.trans k₆).trans k₇).frame (by simp)) |>.trans (frame_body f₈ (by simp))
      |>.trans (frame_body f₉ (by simp))
  have f₈' : Frame [tR s₀, cmpR s₀, stkR s₀, sR s₀ 192 32] s.mem s₈.mem :=
    (((k₁.trans k₂).trans k₃).frame.mono (by simp)) |>.trans (f₄.mono (by simp))
      |>.trans ((((k₅.trans k₆).trans k₇).frame).mono (by simp)) |>.trans (f₈.mono (by simp))
  have hT : bytesAt s₈.mem (TA s₀) 32 = bytesAt s.mem (TA s₀) 32 :=
    frame_bytesAt f₈' (T_disj hp) (by omega)
  have hU₈ : bytesAt s₈.mem (blkA s₀) 32 = stepM s₀ (bytesAt s.mem (blkA s₀) 32) := by
    rw [m₈, digest_self, e₇]; rfl
  have hsep : Mem.Sep (blkA s₀) 32 (TA s₀)
      (Spec.Pbkdf2.xorBytes (bytesAt s₈.mem (TA s₀) 32) (bytesAt s₈.mem (blkA s₀) 32)).length := by
    rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    exact Region.Disjoint.sep (scr_disj s₀ (a := 192) (m := 32) (b := 160) (n := 32) (by omega) (by omega)
      (by omega)) (contains_base (Nat.le_refl _)) (contains_base (Nat.le_refl _))
  have hU₁₀ : bytesAt s₁₀.mem (blkA s₀) 32 = stepM s₀ (bytesAt s.mem (blkA s₀) 32) := by
    rw [u₁₀.mem, m₉, bytesAt_writeBytes_sep _ _ hsep (by omega), hU₈]
  have hT₁₀ : bytesAt s₁₀.mem (TA s₀) 32 =
      Spec.Pbkdf2.xorBytes (bytesAt s.mem (TA s₀) 32) (stepM s₀ (bytesAt s.mem (blkA s₀) 32)) := by
    have := bytesAt_writeBytes_self s₈.mem (TA s₀)
      (Spec.Pbkdf2.xorBytes (bytesAt s₈.mem (TA s₀) 32) (bytesAt s₈.mem (blkA s₀) 32))
      (by rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
    rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length] at this
    rw [u₁₀.mem, m₉, this, hT, hU₈]
  have hle : r ≤ nn s₀ := by have := h.le; omega
  refine ⟨?_, { h₁₀ with edi := ?_, saved := h.saved.frame hp fb, pad := ?_, le := hle, val := ?_ }⟩
  · rw [eval_ne, z₁₀, e₁₀, ofNat_beq_zero (by omega)]
    cases r <;> rfl
  · rw [u₁₀.gpr, e₁₀]
  · rw [← h.pad]
    exact frame_bytesAt fb (body_disj hp (o := 224) (n := 32) (.inr (Nat.le_refl _)) (by omega)) (by omega)
  · rw [h.val, hU₁₀, hT₁₀]; rfl

theorem loop_ok {s₀ : State} (hp : Pre s₀) {n : Nat} {s : State} (h : Inv s₀ n s)
    (hz : s.zf = some (decide (n = 0))) :
    WP isa (.ite .e (.block []) (.loop body .ne)) s (Inv s₀ 0) := by
  refine WP.ite (decide (n = 0)) (by show s.zf = _; rw [hz]) (fun hb => ?_) (fun hb => ?_)
  · obtain rfl : n = 0 := by simpa using hb
    exact WP.block_nil h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hb; omega⟩
    refine WP.loop (fun m s => Inv s₀ (m + 1) s) (fun m s hs => WP.mono (body_ok hp hs) fun s' ⟨he, hi⟩ => ?_) m s h
    cases m with
    | zero => exact .inl ⟨he, hi⟩
    | succ m => exact .inr ⟨he, m, by omega, hi⟩

end VG.Proof.Pbkdf2.X86
