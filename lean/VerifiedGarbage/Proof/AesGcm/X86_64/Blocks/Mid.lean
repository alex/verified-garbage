import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Base
import VerifiedGarbage.Proof.Gcm.Split

/-!
# AES-GCM on whole blocks, x86-64: after the first blocks

Untrusted: everything here is checked by Lean. `Mid s q k ys` holds once the
first `q` blocks are encrypted (or decrypted) and `ys` hashed, with the
arguments kept for the rest after `k` blocks: after the entry (`mid_entry`,
with `q = k = 0`), and after `rest` (`rest_ok`, `k = q`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

section
variable (s : State)

abbrev R : Nat := (s.gpr .rsi).toNat
abbrev ciph : Block → Block := ctxCiph s.mem (K s) (R s)
abbrev cb : Block := blockAt s.mem (C s)
abbrev hk : Block := ctxH s.mem (K s)
abbrev y₀ : Block := blockAt s.mem (Y s)
/-- Where the data left after `q` blocks starts. -/
abbrev dq (q : Nat) : Addr := D s + BitVec.ofNat 64 (16 * q)

end

/-- The first `q` blocks done and `ys` hashed, the arguments kept for what
is left after `k` blocks. -/
structure Mid (s : State) (q k : Nat) (ys : List Block) (st : State) : Prop where
  q_le : q ≤ n s
  rsp : st.gpr .rsp = SP s
  saved : ∀ r ∈ calleeSaved, st.gpr r = s.gpr r
  rd : st.rd = s.rd
  wr : st.wr = s.wr
  kept : Kept s k st.mem
  frame : Frame (wR s) s.mem st.mem
  data : blocksAt st.mem (D s) q = ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) q)
  rest : blocksAt st.mem (dq s q) (n s - q) = blocksAt s.mem (dq s q) (n s - q)
  ctr : blockAt st.mem (C s) = Nat.repeat inc32 q (cb s)
  y : blockAt st.mem (Y s) = ghashFrom (hk s) (y₀ s) ys

section
variable {s : State} (hp : BP s)
include hp

/-- The slots of the arguments are apart from the other regions written. -/
theorem kR'_disj : ∀ r ∈ [cR s, yR s, dR s], (kR' s).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.c_s.sub_right (kR'_sub (s := s))).symm
  · exact (hp.y_s.sub_right (kR'_sub (s := s))).symm
  · exact (hp.d_s.sub_right (kR'_sub (s := s))).symm

omit hp in
theorem Kept.frame {k : Nat} {m m' : Mem} (h : Kept s k m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (kR' s).Disjoint r) : Kept s k m' := by
  have e : ∀ d, 256 ≤ d → d + 8 ≤ 304 → m'.readW (S s + BitVec.ofNat 64 d) 64 = m.readW (S s + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (Offset.contains _ h₁ (by omega) (by omega)) hd (by decide)
  exact ⟨by rw [e 256 (by decide) (by decide)]; exact h.ctx, by rw [e 264 (by decide) (by decide)]; exact h.rounds,
    by rw [e 272 (by decide) (by decide)]; exact h.ctr, by rw [e 280 (by decide) (by decide)]; exact h.y,
    by rw [e 288 (by decide) (by decide)]; exact h.data, by rw [e 296 (by decide) (by decide)]; exact h.n⟩

omit hp in
/-- A frame of `scratch`'s slots keeps a block apart from them. -/
theorem block_kR' {m m' : Mem} (hf : Frame [kR' s] m m') {p : Addr} (hd : (⟨p, 16⟩ : Region).Disjoint (kR' s)) :
    blockAt m' p = blockAt m p :=
  blockAt_frame hf fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd

theorem mid_entry {s₁ : State} (hg : ∀ r, r ≠ .r11 → s₁.gpr r = s.gpr r)
    (hk : Kept s 0 s₁.mem) (hf : Frame [kR' s] s.mem s₁.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) :
    Mid s 0 0 [] s₁ := by
  have hfw : Frame (wR s) s.mem s₁.mem :=
    hf.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨sR s, by simp, kR'_sub⟩
  refine ⟨Nat.zero_le _, hg _ (by decide), fun r hr => hg r ?_, hrd, hwr, hk, hfw, rfl, ?_, ?_, ?_⟩
  · intro e; subst e; simp [calleeSaved] at hr
  · simp only [dq, Nat.mul_zero, BitVec.add_zero, Nat.sub_zero]
    have hd : (⟨D s, 16 * n s⟩ : Region).Disjoint (kR' s) := by
      rw [Nat.mul_comm]; exact (kR'_disj hp (dR s) (by simp)).symm
    exact blocksAt_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) (by
      have := hp.w_d; omega)
  · exact block_kR' hf (kR'_disj hp _ (by simp)).symm
  · exact block_kR' hf (kR'_disj hp _ (by simp)).symm

/-- `Mid` through a frame of `scratch`'s slots that keeps the registers but
`r11`, `r8` and `rax`. -/
theorem Mid.slots {q k k' : Nat} {ys : List Block} {st st' : State} (h : Mid s q k ys st)
    (hg : ∀ r, r ≠ .r11 → r ≠ .r8 → r ≠ .rax → st'.gpr r = st.gpr r) (hk : Kept s k' st'.mem)
    (hf : Frame [kR' s] st.mem st'.mem) (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr) : Mid s q k' ys st' := by
  have hfw : Frame (wR s) st.mem st'.mem :=
    hf.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨sR s, by simp, kR'_sub⟩
  refine ⟨h.q_le, by rw [hg _ (by decide) (by decide) (by decide), h.rsp], fun r hr => ?_, hrd.trans h.rd,
    hwr.trans h.wr, hk, h.frame.trans hfw, ?_, ?_, ?_, ?_⟩
  · rw [hg r (fun e => by subst e; simp [calleeSaved] at hr) (fun e => by subst e; simp [calleeSaved] at hr)
      (fun e => by subst e; simp [calleeSaved] at hr), h.saved r hr]
  · rw [← h.data]
    exact blocksAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (kR'_disj hp (dR s) (by simp)).symm.sub_left (Region.sub_prefix (by have := h.q_le; omega)))
      (by have := hp.w_d; have := h.q_le; omega)
  · rw [← h.rest]
    exact blocksAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (kR'_disj hp (dR s) (by simp)).symm.sub_left (Offset.sub_base (D s) (by have := h.q_le; omega)))
      (by have := hp.w_d; have := h.q_le; omega)
  · rw [← h.ctr]; exact block_kR' hf (kR'_disj hp _ (by simp)).symm
  · rw [← h.y]; exact block_kR' hf (kR'_disj hp _ (by simp)).symm

/-- `rest`: the arguments of the `n mod 16` blocks after the first
`16 ⌊n / 16⌋`. -/
theorem rest_ok {q : Nat} (hq : q = n s - n s % 16) {ys : List Block} {st : State} (h : Mid s q 0 ys st) :
    WP isa (.block rest) st (Mid s q q ys) := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have a₀ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 8) 64 = S s := by
    rw [h.rsp, keep_a hp h.frame]; rfl
  have r₅ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 288) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 296) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have w₅ : InRegions st.wr (S s + BitVec.ofNat 64 288) 8 := by rw [h.wr]; exact s_in hp (by decide)
  have w₆ : InRegions st.wr (S s + BitVec.ofNat 64 296) 8 := by rw [h.wr]; exact s_in hp (by decide)
  have kd := h.kept.data
  have kn := h.kept.n
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.sub_zero] at kd kn
  have e15 := and15 (BitVec.ofNat 64 (n s))
  rw [toNat_ofNat_of_lt hn, imm_eq (by decide)] at e15
  have esub : BitVec.ofNat 64 (n s) - BitVec.ofNat 64 (n s % 16) = BitVec.ofNat 64 q := by
    rw [hq]; exact ofNat_sub (Nat.mod_le _ _) hn
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 2560 → d + 8 ≤ 2560 →
      Mem.Sep (S s + BitVec.ofNat 64 a) (64 / 8) (S s + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep _ h (by omega) (by omega)
  have kp : ∀ d, 256 ≤ d → d + 8 ≤ 288 → ∀ v w : BitVec 64,
      ((st.mem.writeW (S s + BitVec.ofNat 64 288) v).writeW (S s + BitVec.ofNat 64 296) w).readW
        (S s + BitVec.ofNat 64 d) 64 = st.mem.readW (S s + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ v w => by
    rw [Mem.readW_writeW_sep (sep d 296 (.inl (by omega)) (by omega) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep d 288 (.inl (by omega)) (by omega) (by decide)) (by decide)]
  apply WP.of_runBlock
  refine ⟨_, by simp only [rest, argData, argN]; xrun [a₀, hS, r₅, r₆, w₅, w₆, kn, e15, esub, times16_val, kd], ?_⟩
  refine h.slots hp (fun r h1 h2 h3 => by simp [gpr_setReg, gpr_arithFlags, h1, h2, h3]) ?_ ?_ rfl rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [kp 256 (by decide) (by decide)]; exact h.kept.ctx
    · rw [kp 264 (by decide) (by decide)]; exact h.kept.rounds
    · rw [kp 272 (by decide) (by decide)]; exact h.kept.ctr
    · rw [kp 280 (by decide) (by decide)]; exact h.kept.y
    · rw [Mem.readW_writeW_sep (sep 288 296 (.inl (by decide)) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64, BitVec.add_comm]
    · rw [Mem.readW_writeW_self64, hq]; congr 1; omega
  · have c : ∀ d, 256 ≤ d → d + 8 ≤ 304 → (kR' s).Contains (S s + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 288 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 296 (by decide) (by decide))

end

end VG.Proof.AesGcm.X86_64.Blocks
