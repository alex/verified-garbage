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
is left after `k` blocks, in the frame. -/
structure Mid (s : State) (q k : Nat) (ys : List Block) (st : State) : Prop where
  q_le : q ≤ n s
  rsp : st.gpr .rsp = F s
  saved : ∀ r ∈ calleeSaved, r ≠ .rsp → st.gpr r = s.gpr r
  rd : st.rd = s.rd
  wr : st.wr = fR s :: s.wr
  kept : Kept s k st.mem
  frame : Frame (tR s :: wR s) s.mem st.mem
  data : blocksAt st.mem (D s) q = ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) q)
  rest : blocksAt st.mem (dq s q) (n s - q) = blocksAt s.mem (dq s q) (n s - q)
  ctr : blockAt st.mem (C s) = Nat.repeat inc32 q (cb s)
  y : blockAt st.mem (Y s) = ghashFrom (hk s) (y₀ s) ys

section
variable {s : State} (hp : BP s)
include hp

/-- The frame is apart from the regions written. -/
theorem fR_disj : ∀ r ∈ wR s, (fR s).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.t_c.sub_left fR_sub
  · exact hp.t_y.sub_left fR_sub
  · exact hp.t_d.sub_left fR_sub
  · exact hp.t_s.sub_left fR_sub

omit hp in
theorem Kept.frame {k : Nat} {m m' : Mem} (h : Kept s k m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (fR s).Disjoint r) : Kept s k m' := by
  have e : ∀ d, d + 8 ≤ 56 → m'.readW (F s + BitVec.ofNat 64 d) 64 = m.readW (F s + BitVec.ofNat 64 d) 64 :=
    fun d h₁ => hf.readW (Offset.contains_base _ h₁ (by omega)) hd (by decide)
  exact ⟨by rw [e 48 (by decide)]; exact h.ctx, by rw [e 40 (by decide)]; exact h.rounds,
    by rw [e 32 (by decide)]; exact h.ctr, by rw [e 24 (by decide)]; exact h.y,
    by rw [e 16 (by decide)]; exact h.data, by rw [e 8 (by decide)]; exact h.n, by rw [e 0 (by decide)]; exact h.scr⟩

omit hp in
/-- A frame of the frame keeps a block apart from it. -/
theorem block_fR {m m' : Mem} (hf : Frame [fR s] m m') {p : Addr} (hd : (⟨p, 16⟩ : Region).Disjoint (fR s)) :
    blockAt m' p = blockAt m p :=
  blockAt_frame hf fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd

/-- After the frame's push. -/
theorem mid_entry {p : State} (hsp : p.gpr .rsp = F s) (hg : ∀ r, r ≠ .r11 → r ≠ .rsp → p.gpr r = s.gpr r)
    (hk : Kept s 0 p.mem) (hf : Frame [fR s] s.mem p.mem) (hrd : p.rd = s.rd) (hwr : p.wr = fR s :: s.wr) :
    Mid s 0 0 [] p := by
  have hft : Frame (tR s :: wR s) s.mem p.mem :=
    hf.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨tR s, by simp, fR_sub⟩
  refine ⟨Nat.zero_le _, hsp, fun r hr h' => hg r ?_ h', hrd, hwr, hk, hft, rfl, ?_, ?_, ?_⟩
  · intro e; subst e; simp [calleeSaved] at hr
  · simp only [dq, Nat.mul_zero, BitVec.add_zero, Nat.sub_zero]
    have hd : (⟨D s, 16 * n s⟩ : Region).Disjoint (fR s) := by
      rw [Nat.mul_comm]; exact (fR_disj hp (dR s) (by simp)).symm
    exact blocksAt_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) (by
      have := hp.w_d; omega)
  · exact block_fR hf (fR_disj hp _ (by simp)).symm
  · exact block_fR hf (fR_disj hp _ (by simp)).symm

/-- `Mid` through a frame of the frame that keeps the registers but `r8` and
`rax`. -/
theorem Mid.slots {q k k' : Nat} {ys : List Block} {st st' : State} (h : Mid s q k ys st)
    (hg : ∀ r, r ≠ .r8 → r ≠ .rax → st'.gpr r = st.gpr r) (hk : Kept s k' st'.mem)
    (hf : Frame [fR s] st.mem st'.mem) (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr) : Mid s q k' ys st' := by
  have hft : Frame (tR s :: wR s) st.mem st'.mem :=
    hf.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨tR s, by simp, fR_sub⟩
  refine ⟨h.q_le, by rw [hg _ (by decide) (by decide), h.rsp], fun r hr h' => ?_, hrd.trans h.rd,
    hwr.trans h.wr, hk, h.frame.trans hft, ?_, ?_, ?_, ?_⟩
  · rw [hg r (fun e => by subst e; simp [calleeSaved] at hr) (fun e => by subst e; simp [calleeSaved] at hr),
      h.saved r hr h']
  · rw [← h.data]
    exact blocksAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (fR_disj hp (dR s) (by simp)).symm.sub_left (Region.sub_prefix (by have := h.q_le; omega)))
      (by have := hp.w_d; have := h.q_le; omega)
  · rw [← h.rest]
    exact blocksAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (fR_disj hp (dR s) (by simp)).symm.sub_left (Offset.sub_base (D s) (by have := h.q_le; omega)))
      (by have := hp.w_d; have := h.q_le; omega)
  · rw [← h.ctr]; exact block_fR hf (fR_disj hp _ (by simp)).symm
  · rw [← h.y]; exact block_fR hf (fR_disj hp _ (by simp)).symm

omit hp in
/-- A slot of the frame, accessible. -/
theorem f_in {st : State} (hwr : st.wr = fR s :: s.wr) {d : Nat} (h : d + 8 ≤ 56) :
    InRegions st.wr (F s + BitVec.ofNat 64 d) 8 :=
  ⟨fR s, by rw [hwr]; exact List.mem_cons_self .., Offset.contains_base _ h (by omega)⟩

omit hp in
theorem f_in' {st : State} (hwr : st.wr = fR s :: s.wr) {d : Nat} (h : d + 8 ≤ 56) :
    InRegions (st.rd ++ st.wr) (F s + BitVec.ofNat 64 d) 8 := in_left (f_in hwr h)

/-- `rest`: the arguments of the `n mod 16` blocks after the first
`16 ⌊n / 16⌋`. -/
theorem rest_ok {q : Nat} (hq : q = n s - n s % 16) {ys : List Block} {st : State} (h : Mid s q 0 ys st) :
    WP isa (.block rest) st (Mid s q q ys) := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have r₅ := f_in' h.wr (d := 16) (by decide)
  have r₆ := f_in' h.wr (d := 8) (by decide)
  have w₅ := f_in h.wr (d := 16) (by decide)
  have w₆ := f_in h.wr (d := 8) (by decide)
  have kd := h.kept.data
  have kn := h.kept.n
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.sub_zero] at kd kn
  have e15 := and15 (BitVec.ofNat 64 (n s))
  rw [toNat_ofNat_of_lt hn, imm_eq (by decide)] at e15
  have esub : BitVec.ofNat 64 (n s) - BitVec.ofNat 64 (n s % 16) = BitVec.ofNat 64 q := by
    rw [hq]; exact ofNat_sub (Nat.mod_le _ _) hn
  have sep : ∀ a d : Nat, a + 8 ≤ d ∨ d + 8 ≤ a → a + 8 ≤ 56 → d + 8 ≤ 56 →
      Mem.Sep (F s + BitVec.ofNat 64 a) (64 / 8) (F s + BitVec.ofNat 64 d) (64 / 8) :=
    fun a d h ha hd => Offset.sep _ h (by omega) (by omega)
  have kp : ∀ d, d + 8 ≤ 56 → d = 0 ∨ 24 ≤ d → ∀ v w : BitVec 64,
      ((st.mem.writeW (F s + BitVec.ofNat 64 16) v).writeW (F s + BitVec.ofNat 64 8) w).readW
        (F s + BitVec.ofNat 64 d) 64 = st.mem.readW (F s + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ v w => by
    rw [Mem.readW_writeW_sep (sep d 8 (by omega) (by omega) (by decide)) (by decide),
      Mem.readW_writeW_sep (sep d 16 (by omega) (by omega) (by decide)) (by decide)]
  apply WP.of_runBlock
  refine ⟨_, by simp only [rest, argData, argN]; xrun [h.rsp, r₅, r₆, w₅, w₆, kn, e15, esub, times16_val, kd], ?_⟩
  refine h.slots hp (fun r h1 h2 => by simp [gpr_setReg, gpr_arithFlags, h1, h2]) ?_ ?_ rfl rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [kp 48 (by decide) (by decide)]; exact h.kept.ctx
    · rw [kp 40 (by decide) (by decide)]; exact h.kept.rounds
    · rw [kp 32 (by decide) (by decide)]; exact h.kept.ctr
    · rw [kp 24 (by decide) (by decide)]; exact h.kept.y
    · rw [Mem.readW_writeW_sep (sep 16 8 (.inr (by decide)) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64, BitVec.add_comm]
    · rw [Mem.readW_writeW_self64, hq]; congr 1; omega
    · rw [kp 0 (by decide) (by decide)]; exact h.kept.scr
  · have c : ∀ d, d + 8 ≤ 56 → (fR s).Contains (F s + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ => Offset.contains_base _ h₁ (by omega)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 16 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 8 (by decide))

end

end VG.Proof.AesGcm.X86_64.Blocks
