import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Calls

/-!
# ChaCha20-Poly1305 on ARMv7: the prologue

Untrusted: everything here is checked by Lean. Saving the registers, moving
the arguments, copying words of the context, the ChaCha20 state for counter
0, the one-time key and the Poly1305 state for it.
-/

namespace VG.Proof.ChaCha20Poly1305.Arm

open VG VG.Arm VG.Impl.ChaCha20Poly1305.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd saveMem saveList_ok save_sep readW_writeW_save wp_mov
  wp_add wp_ldr wp_str wp_ldrSp op2_imm op2_reg)
open VG.Proof.ChaCha20.Arm (toNat_ofNat_lt)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-! ## More instructions -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_movw {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm.setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movw d imm :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movt {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons rfl (k _ (Upd.setReg _ _ _))

end

/-! ## Saving the registers -/

set_option simprocs false in
theorem saveMem_saved (m : Mem) (B : Addr) (g : Reg → BitVec 32) :
    ∀ p ∈ saved, (saveMem m B g saved).readW (B + BitVec.ofNat 64 p.2) 32 = g p.1 := by
  intro p hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [saved, saveMem, Mem.readW_writeW_self32, readW_writeW_save]

theorem saveMem_frame (s₀ : State) (m : Mem) (g : Reg → BitVec 32) :
    ∀ (l : List (Reg × Nat)), (∀ p ∈ l, savOff ≤ p.2 ∧ p.2 + 4 ≤ savOff + 36) →
      Frame [sub s₀ savOff 36] m (saveMem m (cx s₀) g l) := by
  intro l
  induction l generalizing m with
  | nil => intro _; exact Frame.refl _ _
  | cons p l ih =>
    intro hl
    have h := hl p (by simp)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (w := 32 / 8) h.1 h.2 (by simp [savOff]))).trans
      (ih _ fun q hq => hl q (List.mem_cons_of_mem _ hq))

/-- The moves' results. -/
theorem moves_ok {s₀ : State} (hp : APre s₀) {s : State} (hg : s.gpr = s₀.gpr) (hrd : s.rd = s₀.rd)
    (hsp : s.sp = s₀.sp) (hm : ∀ a, (argR s₀).Contains a 1 → s.mem a = s₀.mem a) :
    WP isa (.block moves) s fun s' => Regs s₀ s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ ∀ r, r ≠ .r7 → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r := by
  unfold moves
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _)
    fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => ?_
  have hsp₄ : s₄.sp = s₀.sp := by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp, hsp]
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [hsp₄]; rfl)
    ⟨argR s₀, by simp [u₄.rd, u₃.rd, u₂.rd, u₁.rd, hrd, hp.rd], Region.contains_self _ _⟩ fun s₅ u₅ => ?_
  refine WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, fun r h7 h8 h9 h10 h11 => ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr, hg]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), hg]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hg]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hg]
  · rw [u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact Mem.readW_congr fun i hi => hm _ (by
      simp only [Region.Contains]
      rw [show stackArgAddr s₀ 0 + BitVec.ofNat 64 i - stackArgAddr s₀ 0 = BitVec.ofNat 64 i by bv_omega,
        toNat_ofNat_lt (by omega)]
      omega)
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₅.other _ h11, u₄.other _ h10, u₃.other _ h9, u₂.other _ h8, u₁.other _ h7]

/-- Saving the registers and moving the arguments. -/
theorem saveMoves_ok {s₀ : State} (hp : APre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s, Regs s₀ s → s.sp = s₀.sp → s.rd = s₀.rd → s.wr = s₀.wr → Saved s₀ s.mem →
      Frame [sub s₀ savOff 36] s₀.mem s.mem → WP isa (.block rest) s Q) :
    WP isa (.block (save ++ moves ++ rest)) s₀ Q := by
  rw [List.append_assoc, show save = saved.map (fun p => Instr.str p.1 .r0 p.2) from rfl]
  refine saveList_ok saved s₀ Q (fun p hp' => ?_) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  · have hb := saved_bound p hp'
    simp only [savOff] at hb
    have := hp.fit_c
    simp only [cP] at this
    refine ⟨by omega, by omega, ?_⟩
    exact hp.in_ctx (by omega)
  have f₁ : Frame [sub s₀ savOff 36] s₀.mem s₁.mem := by
    rw [m₁]; exact saveMem_frame s₀ _ _ _ saved_bound
  refine WP.block_append (WP.mono (moves_ok hp g₁ rd₁ sp₁ fun a ha => f₁ a fun r hr hc => ?_)
    fun s₂ ⟨rg₂, m₂, rd₂, wr₂, sp₂, _⟩ => ?_)
  · simp only [List.mem_singleton] at hr; subst hr
    exact (hp.c_arg.sub_left (sub_ctx s₀ (by simp [savOff]))) a hc ha
  refine k s₂ rg₂ (by rw [sp₂, sp₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) ?_ (by rw [m₂]; exact f₁)
  intro p hp'
  rw [m₂, m₁]
  exact saveMem_saved _ _ _ p hp'

/-! ## Copying words of the context -/

/-- The context may be read and written. -/
def CtxOk (s₀ s : State) : Prop :=
  ∀ a w, a + w ≤ 1024 → InRegions (s.rd ++ s.wr) (off (cx s₀) a) w ∧ InRegions s.wr (off (cx s₀) a) w

theorem Inv.ctxOk {s₀ s : State} (hp : APre s₀) (h : s.rd = s₀.rd) (h' : s.wr = s₀.wr) : CtxOk s₀ s :=
  fun _ _ hw => by rw [h, h']; exact ⟨hp.in_ctx' hw, hp.in_ctx hw⟩

theorem readW_off (m : Mem) (p : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 32 = m.readW (off p d) 32 :=
  readW_writeW_save m p v hd he h

/-- Bytes equal byte by byte. -/
theorem bytesAt_eq_of {m m' : Mem} {p q : Addr} {n : Nat}
    (h : ∀ i < n, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    bytesAt m' q n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.ext_getElem (by simp)
  intro i h₁ _
  simp only [List.getElem_map, List.getElem_range]
  exact h i (by simpa using h₁)

theorem copyWords_step (a b n : Nat) : copyWords a b (n + 1) =
    copyWords a b n ++ ([.ldr .r12 .r7 (a + 4 * n), .str .r12 .r7 (b + 4 * n)] : List Instr) := by
  simp [copyWords, List.range_succ, List.flatMap_append]

/-- `n` words from `ctx + a` to `ctx + b`. -/
theorem copyWords_ok {s₀ : State} (hp : APre s₀) {a b n : Nat} (hab : a + 4 * n ≤ b ∨ b + 4 * n ≤ a)
    (ha : a + 4 * n ≤ 1024) (hb : b + 4 * n ≤ 1024) {s : State} (h7 : s.gpr .r7 = cP s₀)
    (hc : CtxOk s₀ s) :
    WP isa (.block (copyWords a b n)) s fun s' =>
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [sub s₀ b (4 * n)] s.mem s'.mem ∧
      ∀ i < n, s'.mem.readW (off (cx s₀) (b + 4 * i)) 32 = s.mem.readW (off (cx s₀) (a + 4 * i)) 32 := by
  induction n with
  | zero =>
    exact WP.block_nil (M := isa) ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by omega)⟩
  | succ n ih =>
    rw [copyWords_step]
    refine WP.block_append (WP.mono (ih (by omega) (by omega) (by omega))
      fun s₁ ⟨g₁, rd₁, wr₁, sp₁, f₁, w₁⟩ => ?_)
    have hc₁ : CtxOk s₀ s₁ := by rw [CtxOk, rd₁, wr₁]; exact hc
    have h7₁ : s₁.gpr .r7 = cP s₀ := by rw [g₁ _ (by decide), h7]
    refine wp_ldr (a := off (cx s₀) (a + 4 * n)) (by omega) (by rw [h7₁]; exact hp.addr_cP_off (by omega))
      (hc₁ _ 4 (by omega)).1 fun s₂ u₂ => ?_
    refine wp_str (a := off (cx s₀) (b + 4 * n)) (by omega)
      (by rw [u₂.other _ (by decide), h7₁]; exact hp.addr_cP_off (by omega))
      (by rw [u₂.wr]; exact (hc₁ _ 4 (by omega)).2) fun s₃ u₃ => WP.block_nil ?_
    refine ⟨fun r hr => by rw [u₃.gpr, u₂.other r hr, g₁ r hr], by rw [u₃.rd, u₂.rd, rd₁],
      by rw [u₃.wr, u₂.wr, wr₁], by rw [u₃.sp, u₂.sp, sp₁], ?_, fun i hi => ?_⟩
    · rw [u₃.mem, u₂.mem]
      refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _ ?_
      · simp only [List.mem_singleton] at hr; subst hr
        exact Region.sub_prefix (by omega)
      · exact contains_sub s₀ (w := 32 / 8) (by omega) (by omega) (by omega)
    · rw [u₃.mem, u₂.gpr, u₂.mem]
      by_cases h : i = n
      · subst h
        rw [Mem.readW_writeW_self32]
        exact f₁.readW (contains_sub s₀ (k := a + 4 * i) (n := 4) (w := 32 / 8) le_rfl (by omega) (by omega))
          (by simp only [List.mem_singleton, forall_eq]; exact sub_disj s₀ (by omega) (by omega) (by omega))
          (by decide)
      · rw [readW_off _ _ _ (by omega) (by omega) (by omega), w₁ i (by omega)]

/-- Words copied are bytes copied. -/
theorem bytes_of_words {m m' : Mem} {p q : Addr} {n : Nat}
    (h : ∀ k < n, m'.readW (q + BitVec.ofNat 64 (4 * k)) 32 = m.readW (p + BitVec.ofNat 64 (4 * k)) 32) :
    bytesAt m' q (4 * n) = bytesAt m p (4 * n) := by
  refine bytesAt_eq_of fun i hi => ?_
  have e : ∀ a : Addr, a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (4 * (i / 4)) + BitVec.ofNat 64 (i % 4) := by
    intro a
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.div_add_mod]
  rw [e, e, Mem.readW_byte m' (q + BitVec.ofNat 64 (4 * (i / 4))) (Nat.mod_lt _ (by omega)),
    Mem.readW_byte m (p + BitVec.ofNat 64 (4 * (i / 4))) (Nat.mod_lt _ (by omega)), h _ (by omega)]

/-! ## The ChaCha20 state -/

/-- The word `stW k` stores, from memory `m` and the context `c`. -/
def wordOf (m : Mem) (c : Addr) (k : Nat) : BitVec 32 :=
  if k < 4 then consts.getD k 0
  else if k < 12 then m.readW (off c (4 * (k - 4))) 32
  else if k = 12 then 0
  else m.readW (off c (32 + 4 * (k - 13))) 32

theorem stW_ok {s₀ : State} (hp : APre s₀) {k : Nat} (hk : k < 16) {s : State} (h7 : s.gpr .r7 = cP s₀)
    (hc : CtxOk s₀ s) :
    WP isa (.block (stW k)) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) (stOff + 4 * k)) (wordOf s.mem (cx s₀) k) ∧
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have o := (hc (stOff + 4 * k) 4 (by simp [stOff]; omega)).2
  have ea : State.addr (cP s₀ + BitVec.ofNat 32 (stOff + 4 * k)) = off (cx s₀) (stOff + 4 * k) :=
    hp.addr_cP_off (by simp [stOff]; omega)
  unfold stW stSrc wordOf
  by_cases h₁ : k < 4
  · simp only [h₁, ite_true, List.cons_append, List.nil_append]
    refine wp_movw fun s₁ u₁ => wp_movt fun s₂ u₂ => ?_
    refine wp_str (a := off (cx s₀) (stOff + 4 * k)) (by simp [stOff]; omega)
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h7]; exact ea)
      (by rw [u₂.wr, u₁.wr]; exact o) fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem, movw_movt], fun r hr => by
      rw [g₃.gpr, u₂.other r hr, u₁.other r hr], by rw [g₃.rd, u₂.rd, u₁.rd], by rw [g₃.wr, u₂.wr, u₁.wr],
      by rw [g₃.sp, u₂.sp, u₁.sp]⟩
  by_cases h₂ : k < 12
  · simp only [h₁, h₂, ite_true, ite_false, List.cons_append, List.nil_append]
    have i := (hc (4 * (k - 4)) 4 (by omega)).1
    refine wp_ldr (a := off (cx s₀) (4 * (k - 4))) (by omega) (by rw [h7]; exact hp.addr_cP_off (by omega))
      i fun s₁ u₁ => ?_
    refine wp_str (a := off (cx s₀) (stOff + 4 * k)) (by simp [stOff]; omega)
      (by rw [u₁.other _ (by decide), h7]; exact ea) (by rw [u₁.wr]; exact o) fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₁.gpr, u₁.mem], fun r hr => by rw [g₃.gpr, u₁.other r hr],
      by rw [g₃.rd, u₁.rd], by rw [g₃.wr, u₁.wr], by rw [g₃.sp, u₁.sp]⟩
  by_cases h₃ : k = 12
  · simp only [h₃, ite_true]
    refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
    refine wp_str (a := off (cx s₀) (stOff + 4 * 12)) (by simp [stOff])
      (by rw [u₁.other _ (by decide), h7]; exact h₃ ▸ ea) (by rw [u₁.wr]; exact h₃ ▸ o)
      fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₁.gpr, u₁.mem]; simp, fun r hr => by rw [g₃.gpr, u₁.other r hr],
      by rw [g₃.rd, u₁.rd], by rw [g₃.wr, u₁.wr], by rw [g₃.sp, u₁.sp]⟩
  · simp only [h₁, h₂, h₃, ite_false, List.cons_append, List.nil_append]
    have i := (hc (32 + 4 * (k - 13)) 4 (by omega)).1
    refine wp_ldr (a := off (cx s₀) (32 + 4 * (k - 13))) (by omega)
      (by rw [h7]; exact hp.addr_cP_off (by omega)) i fun s₁ u₁ => ?_
    refine wp_str (a := off (cx s₀) (stOff + 4 * k)) (by simp [stOff]; omega)
      (by rw [u₁.other _ (by decide), h7]; exact ea) (by rw [u₁.wr]; exact o) fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₁.gpr, u₁.mem], fun r hr => by rw [g₃.gpr, u₁.other r hr],
      by rw [g₃.rd, u₁.rd], by rw [g₃.wr, u₁.wr], by rw [g₃.sp, u₁.sp]⟩

/-- The context's words `[a, a + 4)` below `stOff`. -/
theorem readW_frame_st {s₀ : State} {m m' : Mem} {n : Nat} (hf : Frame [sub s₀ stOff n] m m') {a : Nat}
    (ha : a + 4 ≤ stOff) (hn : stOff + n ≤ 1024) :
    m'.readW (off (cx s₀) a) 32 = m.readW (off (cx s₀) a) 32 :=
  hf.readW (contains_sub s₀ (k := a) (n := 4) (w := 32 / 8) le_rfl le_rfl (by simp [stOff] at ha hn ⊢; omega))
    (by simp only [List.mem_singleton, forall_eq]
        exact sub_disj s₀ (by omega) (by simp [stOff] at ha hn ⊢; omega) hn) (by decide)

theorem wordOf_frame {s₀ : State} {m m' : Mem} {n : Nat} (hf : Frame [sub s₀ stOff n] m m')
    (hn : stOff + n ≤ 1024) {k : Nat} (hk : k < 16) : wordOf m' (cx s₀) k = wordOf m (cx s₀) k := by
  unfold wordOf
  split_ifs <;> first | rfl | exact readW_frame_st hf (by simp [stOff]; omega) hn

theorem initState_step (j : Nat) : (List.range (j + 1)).flatMap stW = (List.range j).flatMap stW ++ stW j := by
  simp [List.range_succ, List.flatMap_append]

/-- The first `j` words of the ChaCha20 state. -/
theorem initState_ok {s₀ : State} (hp : APre s₀) {j : Nat} (hj : j ≤ 16) {s : State}
    (h7 : s.gpr .r7 = cP s₀) (hc : CtxOk s₀ s) :
    WP isa (.block ((List.range j).flatMap stW)) s fun s' =>
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [sub s₀ stOff (4 * j)] s.mem s'.mem ∧
      ∀ i < j, s'.mem.readW (off (cx s₀) (stOff + 4 * i)) 32 = wordOf s.mem (cx s₀) i := by
  induction j with
  | zero =>
    exact WP.block_nil (M := isa) ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by omega)⟩
  | succ j ih =>
    rw [initState_step]
    refine WP.block_append (WP.mono (ih (by omega)) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, f₁, w₁⟩ => ?_)
    have hc₁ : CtxOk s₀ s₁ := by rw [CtxOk, rd₁, wr₁]; exact hc
    refine WP.mono (stW_ok hp (by omega) (by rw [g₁ _ (by decide), h7]) hc₁)
      fun s₂ ⟨m₂, g₂, rd₂, wr₂, sp₂⟩ => ?_
    refine ⟨fun r hr => by rw [g₂ r hr, g₁ r hr], by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁],
      ?_, fun i hi => ?_⟩
    · rw [m₂]
      refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _ ?_
      · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)
      · exact contains_sub s₀ (w := 32 / 8) (by omega) (by omega) (by simp [stOff]; omega)
    · rw [m₂, wordOf_frame f₁ (by simp [stOff]; omega) (by omega)]
      by_cases h : i = j
      · subst h; exact Mem.readW_writeW_self32 _ _ _
      · rw [readW_off _ _ _ (by simp [stOff]; omega) (by simp [stOff]; omega) (by omega)]
        exact w₁ i (by omega)

theorem consts_eq : ∀ i < 4, consts.getD i 0 = Spec.ChaCha20.constants.getD i 0 := by decide

/-- The words stored are the initial ChaCha20 state for the key, counter 0
and the nonce, if the key and the nonce are as on entry. -/
theorem stateAt_initState {s₀ : State} {m₁ m' : Mem}
    (hk : ∀ a, a + 4 ≤ 44 → m₁.readW (off (cx s₀) a) 32 = s₀.mem.readW (off (cx s₀) a) 32)
    (hw : ∀ i < 16, m'.readW (off (cx s₀) (stOff + 4 * i)) 32 = wordOf m₁ (cx s₀) i) :
    stateAt m' (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Spec.ChaCha20.initState, Vector.getElem_ofFn]
  rw [show off (cx s₀) stOff + BitVec.ofNat 64 (4 * i) = off (cx s₀) (stOff + 4 * i) from off_off _ _ _,
    hw i hi]
  unfold wordOf
  split_ifs with h₁ h₂ h₃
  · exact consts_eq i h₁
  · rw [hk _ (by omega), show (K s₀) = Spec.ChaCha20.bytesAt s₀.mem (cx s₀) 32 from rfl,
      wordLE_bytesAt s₀.mem (cx s₀) (n := 32) (j := i - 4) (by omega)]
  · rfl
  · rw [hk _ (by omega)]
    rw [show (N s₀) = Spec.ChaCha20.bytesAt s₀.mem (cx s₀ + 32) 12 from rfl,
      wordLE_bytesAt s₀.mem (cx s₀ + 32) (n := 12) (j := i - 13) (by omega)]
    refine congrArg (fun a => s₀.mem.readW a 32) ?_
    show cx s₀ + BitVec.ofNat 64 (32 + 4 * (i - 13)) = cx s₀ + 32 + BitVec.ofNat 64 (4 * (i - 13))
    rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl

/-- The first `n ≤ 64` bytes of a ChaCha20 state in memory. -/
theorem bytesAt_serialize (m : Mem) (p : Addr) {n : Nat} (hn : n ≤ 64) :
    bytesAt m p n = (Spec.ChaCha20.serialize (stateAt m p)).take n := by
  apply List.ext_getElem
  · simp [bytesAt, VG.Proof.ChaCha20.length_serialize]; omega
  · intro i h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    have e := VG.Proof.ChaCha20.serialize_stateAt m p (i := i) (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      rw [VG.Proof.ChaCha20.length_serialize]; omega), Option.getD_some] at e
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_take, e]

/-! ## The first block -/

theorem sub_zero (s₀ : State) (n : Nat) : sub s₀ 0 n = ⟨cx s₀, n⟩ := by simp [sub, off]

/-- The regions of the context `[k, k + n)` are within the context, and so
within the regions of the invariant's frame. -/
theorem sub_inv (s₀ : State) {k n : Nat} (h : k + n ≤ 1024) :
    ∃ r' ∈ [ctxR s₀, dR s₀, belR s₀], Region.Sub (sub s₀ k n) r' :=
  ⟨ctxR s₀, by simp, sub_ctx s₀ h⟩

/-- After the first block: the registers saved and moved, and the ChaCha20
state. -/
structure Post1 (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  st : stateAt s.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)
  fctx : Frame [ctxR s₀] s₀.mem s.mem

/-- A frame of `ctx[k, k + n)` is one of the context. -/
theorem frame_ctx {s₀ : State} {m m' : Mem} {k n : Nat} (hf : Frame [sub s₀ k n] m m') (h : k + n ≤ 1024) :
    Frame [ctxR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨ctxR s₀, by simp, sub_ctx s₀ h⟩

/-- The key and the nonce, below the saved registers, are unchanged by a
frame of `ctx[k, k + n)` above them. -/
theorem keyNonce_frame {s₀ : State} {m m' : Mem} {k n : Nat} (hf : Frame [sub s₀ k n] m m')
    (hk : 44 ≤ k) (hn : k + n ≤ 1024) :
    ∀ a, a + 4 ≤ 44 → m'.readW (off (cx s₀) a) 32 = m.readW (off (cx s₀) a) 32 := fun a ha =>
  hf.readW (contains_sub s₀ (k := a) (n := 4) (w := 32 / 8) le_rfl le_rfl (by omega))
    (by simp only [List.mem_singleton, forall_eq]; exact sub_disj s₀ (by omega) (by omega) hn) (by decide)

theorem initStateBlock_ok {s₀ : State} (hp : APre s₀) {s₁ : State} (h : Inv s₀ s₁)
    (hk : ∀ a, a + 4 ≤ 44 → s₁.mem.readW (off (cx s₀) a) 32 = s₀.mem.readW (off (cx s₀) a) 32)
    (hf : Frame [ctxR s₀] s₀.mem s₁.mem) :
    WP isa (.block initState) s₁ fun s₂ => Post1 s₀ s₂ ∧ Frame [sub s₀ stOff (4 * 16)] s₁.mem s₂.mem := by
  refine WP.mono (initState_ok hp (j := 16) le_rfl h.regs.r7 (Inv.ctxOk hp h.rd h.wr))
    fun s₂ ⟨g₂, rd₂, wr₂, sp₂, f₂, w₂⟩ => ⟨⟨?_, stateAt_initState hk w₂,
      hf.trans (frame_ctx f₂ (by simp [stOff]))⟩, f₂⟩
  have hk₂ : Kept [sub s₀ stOff (4 * 16)] s₁ s₂ :=
    ⟨fun r hr _ => g₂ r (by rintro rfl; simp [preserved] at hr), sp₂, rd₂, wr₂, f₂⟩
  exact h.step1 hk₂ (by simp [stOff]) (by simp [stOff, savOff])

theorem block1_seal_ok {s₀ : State} (hp : APre s₀) :
    WP isa (.block (save ++ moves ++ initState)) s₀ (Post1 s₀) :=
  saveMoves_ok hp fun s₁ rg sp rd wr sv f₁ => WP.mono (initStateBlock_ok hp
    ⟨rg, sp, rd, wr, sv, f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_inv s₀ (by simp [savOff])⟩
    (keyNonce_frame f₁ (by simp [savOff]) (by simp [savOff])) (frame_ctx f₁ (by simp [savOff]))) fun _ h => h.1

/-- `open`'s first block also keeps the tag received. -/
structure Post1o (s₀ : State) (s : State) : Prop extends Post1 s₀ s where
  rt : bytesAt s.mem (off (cx s₀) rtagOff) 16 = T0 s₀

theorem block1_open_ok {s₀ : State} (hp : APre s₀) :
    WP isa (.block (save ++ moves ++ copyWords 48 rtagOff 4 ++ initState)) s₀ (Post1o s₀) := by
  rw [List.append_assoc (save ++ moves)]
  refine saveMoves_ok hp fun s₁ rg sp rd wr sv f₁ => ?_
  have i₁ : Inv s₀ s₁ := ⟨rg, sp, rd, wr, sv, f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_inv s₀ (by simp [savOff])⟩
  refine WP.block_append (WP.mono (copyWords_ok hp (a := 48) (b := rtagOff) (n := 4) (by simp [rtagOff])
    (by omega) (by simp [rtagOff]) rg.r7 (Inv.ctxOk hp rd wr)) fun s₂ ⟨g₂, rd₂, wr₂, sp₂, f₂, w₂⟩ => ?_)
  have hk₂ : Kept [sub s₀ rtagOff (4 * 4)] s₁ s₂ :=
    ⟨fun r hr _ => g₂ r (by rintro rfl; simp [preserved] at hr), sp₂, rd₂, wr₂, f₂⟩
  have i₂ := i₁.step1 hk₂ (by simp [rtagOff]) (by simp [rtagOff, savOff])
  have kn₂ := keyNonce_frame f₂ (by simp [rtagOff]) (by simp [rtagOff])
  have kn₁ := keyNonce_frame f₁ (by simp [savOff]) (by simp [savOff])
  refine WP.mono (initStateBlock_ok hp i₂ (fun a ha => by rw [kn₂ a ha, kn₁ a ha])
    ((frame_ctx f₁ (by simp [savOff])).trans (frame_ctx f₂ (by simp [rtagOff]))))
    fun s₃ ⟨h₃, f₃⟩ => ⟨h₃, ?_⟩
  -- The tag received: words copied from `ctx[48, 64)`, which the save did
  -- not touch, and not overwritten by the ChaCha20 state.
  rw [bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (a := rtagOff) (n := 16) (by simp [rtagOff, stOff]) (by simp [rtagOff])
        (by simp [stOff])) (by omega)]
  have e : bytesAt s₂.mem (off (cx s₀) rtagOff) (4 * 4) = bytesAt s₁.mem (off (cx s₀) 48) (4 * 4) :=
    bytes_of_words fun k hk => by rw [off_add, off_add]; exact w₂ k hk
  rw [show (16 : Nat) = 4 * 4 from rfl, e]
  exact bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (a := 48) (n := 4 * 4) (by simp [savOff]) (by omega) (by simp [savOff])) (by omega)

/-! ## The one-time key -/

theorem hr7 {s₀ s : State} (h : Inv s₀ s) : s.gpr .r7 = cP s₀ := h.regs.r7

/-- `r0 = r7 + stOff`, `r1 = r7`. -/
theorem kgA_ok {s₀ : State} {s : State} (h : Inv s₀ s) :
    WP isa (.block [.dp .add .r0 .r7 (.imm (BitVec.ofNat 32 stOff)), .mov .r1 (.reg .r7)]) s fun s' =>
      s'.gpr .r0 = ptr s₀ stOff ∧ s'.gpr .r1 = cP s₀ ∧ Kept [] s s' := by
  have core : WP isa (.block [.dp .add .r0 .r7 (.imm (BitVec.ofNat 32 stOff)), .mov .r1 (.reg .r7)]) s
      fun s' => s'.gpr .r0 = ptr s₀ stOff ∧ s'.gpr .r1 = cP s₀ ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.mem = s.mem :=
    wp_add (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr, hr7 h], by rw [u₂.gpr, u₁.other _ (by decide), hr7 h],
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept core (by simp [dstOf, preserved]))
    fun s' ⟨⟨h0, h1, hrd, hwr, hm⟩, hg, hsp⟩ => ⟨h0, h1, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

/-- After the one-time key is computed. -/
structure PostK (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  st : stateAt s.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)
  key : bytesAt s.mem (off (cx s₀) keyOff) 32 = otk s₀

theorem keyGen_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Post1 s₀ s) :
    WP isa keyGen s fun s' => PostK s₀ s' ∧ Frame [sub s₀ 0 256, sub s₀ keyOff 32] s.mem s'.mem := by
  unfold keyGen
  refine WP.seq (WP.mono (kgA_ok h.inv) fun s₁ ⟨h0, h1, k₁⟩ => ?_)
  have i₁ := h.inv.step0 k₁
  have m₁ := k₁.mem_eq
  refine WP.seq (block_call h0 h1 (by
      rw [hp.addr_ptr (by simp [stOff]), ← sub_zero]
      exact sub_disj s₀ (a := 0) (n := 256) (by simp [stOff]) (by omega) (by simp [stOff]))
    (by rw [hp.ptr_toNat (by simp [stOff])]; have := hp.fit_c; simp [stOff]; omega)
    (by have := hp.fit_c; omega)
    (by rw [hp.addr_ptr (by simp [stOff]), ← sub_zero]
        exact covers2 hp i₁.wr (a := 0) (n := 256) (b := stOff) (m := 64) (by omega) (by simp [stOff]))
    (by rw [← sub_zero]; exact covers1 hp i₁.wr (a := 0) (n := 256) (by omega)) fun s₂ k₂ r1₂ blk₂ => ?_)
  rw [← sub_zero] at k₂
  have i₂ := i₁.step1 k₂ (by omega) (by simp [savOff])
  -- `mov r7, r1`, then the copy.
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => ?_
  have h7₃ : s₃.gpr .r7 = cP s₀ := by rw [u₃.gpr, r1₂]
  refine WP.mono (copyWords_ok hp (a := 0) (b := keyOff) (n := 8) (by simp [keyOff]) (by omega)
    (by simp [keyOff]) h7₃ (Inv.ctxOk hp (by rw [u₃.rd, i₂.rd]) (by rw [u₃.wr, i₂.wr])))
    fun s₄ ⟨g₄, rd₄, wr₄, sp₄, f₄, w₄⟩ => ?_
  have g₃ : ∀ r, s₃.gpr r = s₂.gpr r := fun r => by
    by_cases e : r = .r7
    · subst e; rw [h7₃, i₂.regs.r7]
    · exact u₃.other r e
  have hk₄ : Kept [sub s₀ keyOff (4 * 8)] s₂ s₄ :=
    ⟨fun r hr _ => by rw [g₄ r (by rintro rfl; simp [preserved] at hr), g₃ r],
      by rw [sp₄, u₃.sp], by rw [rd₄, u₃.rd], by rw [wr₄, u₃.wr], by rw [← u₃.mem]; exact f₄⟩
  have i₄ := i₂.step1 hk₄ (by simp [keyOff]) (by simp [keyOff, savOff])
  refine ⟨⟨i₄, ?_, ?_⟩, ?_⟩
  · -- The ChaCha20 state is outside both writes.
    rw [stateAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by simp [stOff, keyOff]) (by simp [stOff]) (by simp [keyOff])),
      u₃.mem, stateAt_frame k₂.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (a := stOff) (n := 64) (b := 0) (m := 256) (by simp [stOff]) (by simp [stOff])
          (by omega)), m₁, h.st]
  · have e : bytesAt s₄.mem (off (cx s₀) keyOff) (4 * 8) = bytesAt s₃.mem (off (cx s₀) 0) (4 * 8) :=
      bytes_of_words fun k hk => by rw [off_add, off_add]; exact w₄ k hk
    rw [show (32 : Nat) = 4 * 8 from rfl, e, u₃.mem, off_zero, bytesAt_serialize _ _ (by omega), blk₂, m₁,
      hp.addr_ptr (by simp [stOff]), h.st]
    rfl
  · refine (k₁.frame.sub fun _ hr => absurd hr List.not_mem_nil).trans ((k₂.frame.sub fun r hr => ?_).trans ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · rw [← u₃.mem]
      exact f₄.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩

/-! ## The Poly1305 state -/

/-- `r0 = r7`, `r1 = r7 + keyOff`. -/
theorem piA_ok {s₀ : State} {s : State} (h : Inv s₀ s) :
    WP isa (.block [.mov .r0 (.reg .r7), .dp .add .r1 .r7 (.imm (BitVec.ofNat 32 keyOff))]) s fun s' =>
      s'.gpr .r0 = cP s₀ ∧ s'.gpr .r1 = ptr s₀ keyOff ∧ Kept [] s s' := by
  have core : WP isa (.block [.mov .r0 (.reg .r7), .dp .add .r1 .r7 (.imm (BitVec.ofNat 32 keyOff))]) s
      fun s' => s'.gpr .r0 = cP s₀ ∧ s'.gpr .r1 = ptr s₀ keyOff ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.mem = s.mem :=
    wp_mov (op2_reg _ _) fun s₁ u₁ => wp_add (op2_imm (by decide)) fun s₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr, hr7 h], by rw [u₂.gpr, u₁.other _ (by decide), hr7 h],
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.mem, u₁.mem]⟩
  exact WP.mono (WP.kept core (by simp [dstOf, preserved]))
    fun s' ⟨⟨h0, h1, hrd, hwr, hm⟩, hg, hsp⟩ => ⟨h0, h1, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩

/-- `mov r7, r0` with `r0` the context. -/
theorem anchor_ok {s₀ : State} {s : State} (h : Inv s₀ s) {r : Reg} (hr : s.gpr r = cP s₀) :
    WP isa (.block [.mov .r7 (.reg r)]) s fun s' => Inv s₀ s' ∧ Kept [] s s' := by
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => WP.block_nil ?_
  have g : ∀ q, s₁.gpr q = s.gpr q := fun q => by
    by_cases e : q = .r7
    · subst e; rw [u₁.gpr, hr, hr7 h]
    · exact u₁.other q e
  have hk : Kept [] s s₁ := ⟨fun q _ _ => g q, u₁.sp, u₁.rd, u₁.wr, by rw [u₁.mem]; exact Frame.refl _ _⟩
  exact ⟨h.step0 hk, hk⟩

theorem polyInit_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s)
    (hkey : bytesAt s.mem (off (cx s₀) keyOff) 32 = otk s₀) :
    WP isa polyInit s fun s' => Inv s₀ s' ∧ Kept [sub s₀ 0 128] s s' ∧ Repr s'.mem (cx s₀) (otk s₀) [] := by
  unfold polyInit
  refine WP.seq (WP.mono (piA_ok h) fun s₁ ⟨h0, h1, k₁⟩ => ?_)
  have i₁ := h.step0 k₁
  refine WP.seq (init_call h0 h1 (by
      rw [hp.addr_ptr (by simp [keyOff]), ← sub_zero]
      exact sub_disj s₀ (a := 0) (n := 128) (by simp [keyOff]) (by omega) (by simp [keyOff]))
    (by have := hp.fit_c; omega)
    (by rw [hp.ptr_toNat (by simp [keyOff])]; have := hp.fit_c; simp [keyOff]; omega)
    (by rw [hp.addr_ptr (by simp [keyOff]), ← sub_zero]
        exact covers2 hp i₁.wr (a := 0) (n := 128) (b := keyOff) (m := 32) (by omega) (by simp [keyOff]))
    (by rw [← sub_zero]; exact covers1 hp i₁.wr (a := 0) (n := 128) (by omega)) fun s₂ k₂ r0₂ repr₂ => ?_)
  rw [← sub_zero] at k₂
  have i₂ := i₁.step1 k₂ (by omega) (by simp [savOff])
  refine WP.mono (anchor_ok i₂ r0₂) fun s₃ ⟨i₃, k₃⟩ => ⟨i₃, (k₁.sub fun _ hr => absurd hr List.not_mem_nil).trans
    (k₂.trans (k₃.sub fun _ hr => absurd hr List.not_mem_nil)), ?_⟩
  rw [k₃.mem_eq]
  rw [hp.addr_ptr (by simp [keyOff]), k₁.mem_eq, hkey] at repr₂
  exact repr₂

end VG.Proof.ChaCha20Poly1305.Arm
