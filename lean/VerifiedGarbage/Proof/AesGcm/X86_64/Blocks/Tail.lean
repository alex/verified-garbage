import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Mid

/-!
# AES-GCM on whole blocks, x86-64: the blocks left

Untrusted: everything here is checked by Lean. From `Mid s q q ys`, the
`n - q` blocks left, if any, are encrypted with `vg_aes_ctr32` and hashed
with `vg_ghash` (`encTail_ok`), or hashed and then decrypted (`decTail_ok`),
with the arguments reloaded from `scratch` for each call (`ctrArgs_ok`,
`ghArgs_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

/-- A prefix of a region that `rs` covers. -/
theorem covers_prefix {b : Addr} {k L : Nat} {rs : List Region} (h : Covers [⟨b, L⟩] rs) (hk : k ≤ L) :
    Covers [⟨b, k⟩] rs := fun a m ⟨r, hr, hc⟩ => by
  simp only [List.mem_singleton] at hr; subst hr
  exact h a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩

/-- `covers_off` without a bound on the region's length. -/
theorem covers_off' {p : Addr} {k d m : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + m ≤ k)
    (hd' : d < 2 ^ 64) : Covers [⟨p + BitVec.ofNat 64 d, m⟩] rs := by
  intro a j ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  refine h a j ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [Region.Contains] at hc ⊢
  have e : a - p = (a - (p + BitVec.ofNat 64 d)) + BitVec.ofNat 64 d := by
    rw [Offset.sub_add_eq]; exact (BitVec.sub_add_cancel _ _).symm
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) hd']
  have := Nat.mod_le ((a - (p + BitVec.ofNat 64 d)).toNat + d) (2 ^ 64)
  omega

/-- What the calls need of the state: the stack pointer, the permissions, the
arguments kept for what is left after `q` blocks, and `scratch` on the stack. -/
structure Ready (s : State) (q : Nat) (st : State) : Prop where
  rsp : st.gpr .rsp = SP s
  rd : st.rd = s.rd
  wr : st.wr = s.wr
  kept : Kept s q st.mem
  arg : st.mem.readW (SP s + BitVec.ofNat 64 8) 64 = S s

/-- What the calls' working space is. -/
abbrev S5 (s : State) : Addr := S s + BitVec.ofNat 64 512

section
variable {s : State} (hp : BP s)
include hp

theorem cov_k : Covers [kR s] (s.rd ++ s.wr) := covers_of_mem (by rw [hp.rd]; simp)
theorem cov_c : Covers [cR s] s.wr := covers_of_mem (by rw [hp.wr]; simp)
theorem cov_y : Covers [yR s] s.wr := covers_of_mem (by rw [hp.wr]; simp)
theorem cov_d : Covers [dR s] s.wr := covers_of_mem (by rw [hp.wr]; simp)
theorem cov_s : Covers [sR s] s.wr := covers_of_mem (by rw [hp.wr]; simp)

omit hp in
/-- The data left after `q` blocks is in the data. -/
theorem dq_sub {q : Nat} (hq : q ≤ n s) : Region.Sub ⟨dq s q, 16 * (n s - q)⟩ (dR s) :=
  Offset.sub_base _ (by omega)

omit hp in
theorem s5_sub {k : Nat} (hk : k ≤ 2048) : Region.Sub ⟨S5 s, k⟩ (sR s) := Offset.sub_base _ (by omega)

/-- The head of `tail`: `r8` the number of blocks left, `ZF` if none. -/
theorem tailHead_ok {q : Nat} {ys : List Block} {st : State} (h : Mid s q q ys st) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 8)), .mov .r8 (.mem (at_ .r11 argN)), .alu .test .r8 (.reg .r8)])
      st fun st' => Mid s q q ys st' ∧ st'.zf = some (decide (n s - q = 0)) := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have a₀ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 8) 64 = S s := by rw [h.rsp, keep_a hp h.frame]; rfl
  have r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 296) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have hz := and_self_beq (show n s - q < 2 ^ 64 by omega)
  apply WP.of_runBlock
  refine ⟨_, by simp only [argN]; xrun [a₀, hS, r₆, h.kept.n], ?_, by simp only [zf_arithFlags, hz]⟩
  exact h.slots hp (fun r h1 h2 h3 => by simp [gpr_setReg, gpr_arithFlags, h1, h2]) h.kept (Frame.refl _ _) rfl rfl

theorem Mid.ready {q : Nat} {ys : List Block} {st : State} (h : Mid s q q ys st) : Ready s q st :=
  ⟨h.rsp, h.rd, h.wr, h.kept, by rw [keep_a hp h.frame]; rfl⟩

/-- The arguments of `vg_aes_ctr32` on the `n - q` blocks left. -/
theorem ctrArgs_ok {q : Nat} {st : State} (h : Ready s q st) (hq : q < n s) :
    WP isa (.block ctrArgs) st fun st' => CtrCall st' (K s) (C s) (dq s q) (S5 s) (R s) (n s - q) ∧
      Ready s q st' ∧ (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.mem = st.mem := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have hw := hp.w_d
  have a₀ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 8) 64 = S s := by rw [h.rsp, h.arg]
  have r₁ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 256) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₂ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 264) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₃ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 272) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₅ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 288) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 296) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have hdq : Region.Sub ⟨dq s q, 16 * (n s - q)⟩ (dR s) := dq_sub (by omega)
  have p240 : Region.Sub ⟨K s, 240⟩ (kR s) := Region.sub_prefix (by decide)
  have s48 : Region.Sub ⟨S5 s, 2048⟩ (sR s) := s5_sub (by decide)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [ctrArgs, argCtx, argRounds, argCtr, argData, argN]
    xrun [a₀, hS, r₁, r₂, r₃, r₅, r₆, h.kept.ctx, h.kept.rounds, h.kept.ctr, h.kept.data, h.kept.n], ?_⟩
  refine ⟨⟨by simp [gpr_setReg], by simp [gpr_setReg, R], by simp [gpr_setReg], by simp [gpr_setReg, dq],
    by simp [gpr_setReg], by simp [gpr_setReg, gpr_arithFlags, S5], hp.rounds, ?_,
    hp.k_c.sub_left p240, (hp.k_d.sub_left p240).sub_right hdq, (hp.k_s.sub_left p240).sub_right s48,
    hp.c_d.sub_right hdq, hp.c_s.sub_right s48, (hp.d_s.sub_left hdq).sub_right s48, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨by simp [gpr_setReg, gpr_arithFlags, h.rsp], h.rd, h.wr, h.kept, h.arg⟩, fun r hr => ?_, rfl⟩
  · simp only [dq, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := Nat.mod_le ((D s).toNat + 16 * q % 2 ^ 64) (2 ^ 64)
    rw [Nat.mod_eq_of_lt (a := 16 * q) (by omega)]; omega
  all_goals try simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ↓reduceIte, h.rsp]
  · exact hp.t_k.sub_right p240
  · exact hp.t_c
  · exact hp.t_d.sub_right hdq
  · exact hp.t_s.sub_right s48
  · simp only [rd_setReg, wr_setReg, rd_arithFlags, wr_arithFlags, h.rd, h.wr]
    refine covers_cons (covers_prefix (cov_k hp) (by decide)) (covers_cons (covers_left (cov_c hp))
      (covers_cons (covers_left (covers_off' (cov_d hp) (by omega) (by omega)))
        (covers_left (covers_off (cov_s hp) (by decide) (by decide)))))
  · simp only [wr_setReg, wr_arithFlags, h.wr]
    exact covers_cons (cov_c hp) (covers_cons (covers_off' (cov_d hp) (by omega) (by omega))
      (covers_off (cov_s hp) (by decide) (by decide)))
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]

/-- The data is not all of memory: the key context is apart from it. -/
theorem n16_lt : n s * 16 < 2 ^ 64 := by
  have hw := hp.w_d
  refine Nat.lt_of_not_le fun hge => hp.k_d (K s) ?_ ?_
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · simp only [Region.Contains]
    have := (K s - D s).isLt
    omega

/-- The arguments of `vg_ghash` on the `n - q` blocks left. -/
theorem ghArgs_ok {q : Nat} {st : State} (h : Ready s q st) (hq : q < n s) :
    WP isa (.block ghArgs) st fun st' => GhCall st' (K s + BitVec.ofNat 64 240) (Y s) (dq s q) (S5 s) (n s - q) ∧
      Ready s q st' ∧ (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.mem = st.mem := by
  have hn : n s < 2 ^ 64 := (s.gpr .r9).isLt
  have hw := hp.w_d
  have h16 := n16_lt hp
  have a₀ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp
  have hS : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 8) 64 = S s := by rw [h.rsp, h.arg]
  have r₁ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 256) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₄ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 280) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₅ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 288) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have r₆ : InRegions (st.rd ++ st.wr) (S s + BitVec.ofNat 64 296) 8 := by rw [h.rd, h.wr]; exact s_in' hp (by decide)
  have hdq : Region.Sub ⟨dq s q, 16 * (n s - q)⟩ (dR s) := dq_sub (by omega)
  have pH : Region.Sub ⟨K s + BitVec.ofNat 64 240, 16⟩ (kR s) := Offset.sub_base _ (by decide)
  have s16 : Region.Sub ⟨S5 s, 256⟩ (sR s) := s5_sub (by decide)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [ghArgs, argCtx, argY, argData, argN]
    xrun [a₀, hS, r₁, r₄, r₅, r₆, h.kept.ctx, h.kept.y, h.kept.data, h.kept.n], ?_⟩
  refine ⟨⟨by simp [gpr_setReg, gpr_arithFlags], by simp [gpr_setReg], by simp [gpr_setReg, dq],
    by simp [gpr_setReg], by simp [gpr_setReg, gpr_arithFlags, S5], by omega,
    hp.k_y.sub_left pH, (hp.k_s.sub_left pH).sub_right s16, hp.y_d.sub_right hdq, hp.y_s.sub_right s16,
    (hp.d_s.sub_left hdq).sub_right s16, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨by simp [gpr_setReg, gpr_arithFlags, h.rsp], h.rd, h.wr, h.kept, h.arg⟩, fun r hr => ?_, rfl⟩
  all_goals try simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ↓reduceIte, h.rsp]
  · exact hp.t_k.sub_right pH
  · exact hp.t_y
  · exact hp.t_d.sub_right hdq
  · exact hp.t_s.sub_right s16
  · simp only [rd_setReg, wr_setReg, rd_arithFlags, wr_arithFlags, h.rd, h.wr]
    refine covers_cons (covers_off (cov_k hp) (by decide) (by decide))
      (covers_cons (covers_left (covers_off' (cov_d hp) (by omega) (by omega)))
      (covers_cons (covers_left (cov_y hp)) (covers_left (covers_off (cov_s hp) (by decide) (by decide)))))
  · simp only [wr_setReg, wr_arithFlags, h.wr]
    exact covers_cons (cov_y hp) (covers_off (cov_s hp) (by decide) (by decide))
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]

end

end VG.Proof.AesGcm.X86_64.Blocks
