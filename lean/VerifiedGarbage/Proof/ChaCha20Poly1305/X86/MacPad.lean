import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.Calls

/-!
# ChaCha20-Poly1305 on x86 (32-bit): absorbing padded data

Untrusted: everything here is checked by Lean. `absorbOne k` absorbs the 16
bytes at `ctx + k`; `macPad p n` absorbs the bytes whose address and length
are the stack arguments at `esp + p` and `esp + n`, and zeros to a multiple
of 16: `msg ++ x ++ pad16 x`. Each stage is stated separately, for the
constant-time proof.
-/

namespace VG.Proof.ChaCha20Poly1305.X86

open VG VG.X86 VG.Impl.ChaCha20Poly1305.X86
open VG.Impl.ChaCha20.X86 (at_)
open VG.Proof.ChaCha20.X86 (contains_off toNat_ofNat_lt)
open VG.Proof.Poly1305.X86 (wp_movm wp_store wp_movzx8 wp_store8 wp_addx wp_subx wp_movi wp_mov wp_andx
  wp_shr Upd Mupd readSrc_imm readSrc_reg writeW8_apply writeW32_zero_apply add_ofNat_one addr_zero_add)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20Poly1305 (pad16)

/-! ## Frames within the working space -/

theorem work_sub (s₀ : State) {k n : Nat} (h₁ : 64 ≤ k) (h₂ : k + n ≤ 1024) :
    ∃ r' ∈ [workR s₀, dR s₀, stkR s₀], Region.Sub (sub s₀ k n) r' :=
  ⟨workR s₀, by simp, sub_sub s₀ h₁ (by omega) (by omega)⟩

theorem stk_work (s₀ : State) : ∃ r' ∈ [workR s₀, dR s₀, stkR s₀], Region.Sub (stkR s₀) r' :=
  ⟨stkR s₀, by simp, fun _ h => h⟩

/-- The invariant survives a part that writes only `ctx[k, k + n)` (apart from
the saved registers) and the stack, and keeps `edi`. -/
theorem Inv.part {s₀ s s' : State} (hp : APre s₀) (h : Inv s₀ s) (h' : At s₀ s')
    (hedi : s'.gpr .edi = s.gpr .edi) {k n : Nat} (h₁ : 64 ≤ k) (h₂ : k + n ≤ 1024)
    (h₃ : k + n ≤ 592 ∨ 608 ≤ k) (hf : Frame [sub s₀ k n, stkR s₀] s.mem s'.mem) : Inv s₀ s' :=
  h.step hedi (by rw [h'.esp, h.esp]) (by rw [h'.rd, h.rd]) (by rw [h'.wr, h.wr]) hf
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact work_sub s₀ h₁ h₂
      · exact stk_work s₀)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj s₀ (by omega) (by omega) h₂
      · exact (hp.stk_sub (by omega)).symm)

/-! ## Absorbing 16 bytes of the context -/

theorem bsrc_ctx {s₀ : State} (hp : APre s₀) {k : Nat} (hk : k + 16 ≤ 448 ∨ (576 ≤ k ∧ k + 16 ≤ 1024)) :
    BSrc s₀ (C32 s₀ k) 16 := by
  have := hp.fit_c
  refine ⟨by rw [hp.cNat (by omega)]; omega, ?_, ?_,
    ⟨ctxR s₀, by simp [hp.wr], k, hp.c64 (by omega), by show k + 16 ≤ 1024; omega⟩⟩
  · rw [hp.c64 (by omega)]; exact sub_disj s₀ (by omega) (by omega) (by omega)
  · rw [hp.c64 (by omega)]; exact hp.stk_sub (by omega)

/-- Ready to call `vg_poly1305_blocks` for the 16 bytes at `ctx + k`. -/
structure OneA (s₀ : State) (k : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  eax : s.gpr .eax = BitVec.ofNat 32 1
  ecx : s.gpr .ecx = C32 s₀ k
  edx : s.gpr .edx = C32 s₀ 448

theorem oneA_ok {s₀ : State} {s : State} (h : Inv s₀ s) (k : Nat) :
    WP isa (.block ([.mov .eax (.imm 1)] ++ ptr .ecx .edi k ++ ptr .edx .edi 448)) s fun s' =>
      OneA s₀ k s' ∧ s'.mem = s.mem := by
  rw [show ([.mov .eax (.imm 1)] ++ ptr .ecx .edi k ++ ptr .edx .edi 448 : List Instr) =
    .mov .eax (.imm 1) :: (ptr .ecx .edi k ++ ptr .edx .edi 448) from rfl]
  refine wp_movi fun s₁ u₁ _ => ?_
  refine WP.block_append (WP.mono (ptr_ok .ecx .edi k s₁) fun s₂ ⟨e₂, g₂, rd₂, wr₂, m₂⟩ => ?_)
  refine WP.mono (ptr_ok .edx .edi 448 s₂) fun s₃ ⟨e₃, g₃, rd₃, wr₃, m₃⟩ => ?_
  have edi : s₂.gpr .edi = CX s₀ := by rw [g₂ _ (by decide), u₁.other _ (by decide), h.edi]
  have mm : s₃.mem = s.mem := by rw [m₃, m₂, u₁.mem]
  refine ⟨⟨h.step (by rw [g₃ _ (by decide), g₂ _ (by decide), u₁.other _ (by decide)])
      (by rw [g₃ _ (by decide), g₂ _ (by decide), u₁.other _ (by decide)])
      (by rw [rd₃, rd₂, u₁.rd]) (by rw [wr₃, wr₂, u₁.wr]) (rs := []) (by rw [mm]; exact Frame.refl _ _)
      (by simp) (by simp),
    by rw [g₃ _ (by decide), g₂ _ (by decide), u₁.gpr]; rfl,
    by rw [g₃ _ (by decide), e₂, u₁.other _ (by decide), h.edi], by rw [e₃, edi]⟩, mm⟩

theorem absorbOne_eq (k : Nat) : absorbOne k =
    .seq (.block ([.mov .eax (.imm 1)] ++ ptr .ecx .edi k ++ ptr .edx .edi 448))
      (callWith [.eax, .ecx, .edx] "vg_poly1305_blocks" Impl.Poly1305.X86.blocks) := rfl

theorem oneB_ok {s₀ : State} (hp : APre s₀) {k : Nat} (hk : k + 16 ≤ 448 ∨ (576 ≤ k ∧ k + 16 ≤ 1024))
    {s : State} (h : OneA s₀ k s) :
    WP isa (callWith [.eax, .ecx, .edx] "vg_poly1305_blocks" Impl.Poly1305.X86.blocks) s fun s' =>
      Inv s₀ s' ∧ Frame [sub s₀ 448 128, stkR s₀] s.mem s'.mem ∧
      ∀ key msg, Repr s.mem (cx s₀ + BitVec.ofNat 64 448) key msg →
        Repr s'.mem (cx s₀ + BitVec.ofNat 64 448) key (msg ++ bytesAt s.mem (cx s₀ + BitVec.ofNat 64 k) 16) := by
  have := hp.fit_c
  refine blocks_call hp h.inv.at (n := 1) (by decide) (bsrc_ctx hp hk) h.edx h.ecx h.eax
    fun s' at' cs' f' repr' => ⟨h.inv.part hp at' (cs' .edi (by simp [calleeSaved])) (k := 448) (n := 128)
      (by omega) (by omega) (by omega) f', f', fun key msg hr => ?_⟩
  have := repr' key msg hr
  rwa [hp.c64 (by omega)] at this

theorem absorbOne_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) {k : Nat}
    (hk : k + 16 ≤ 448 ∨ (576 ≤ k ∧ k + 16 ≤ 1024)) :
    WP isa (absorbOne k) s fun s' =>
      Inv s₀ s' ∧ Frame [sub s₀ 448 128, stkR s₀] s.mem s'.mem ∧
      ∀ key msg, Repr s.mem (cx s₀ + BitVec.ofNat 64 448) key msg →
        Repr s'.mem (cx s₀ + BitVec.ofNat 64 448) key (msg ++ bytesAt s.mem (cx s₀ + BitVec.ofNat 64 k) 16) := by
  rw [absorbOne_eq]
  exact WP.seq (WP.mono (oneA_ok h k) fun s₁ ⟨h₁, m₁⟩ => by
    rw [← m₁]; exact oneB_ok hp hk h₁)

/-! ## The bytes absorbed -/

/-- What `macPad` needs of the `len` bytes at `P` it absorbs. -/
structure Src (s₀ : State) (P : BitVec 32) (len : Nat) : Prop where
  fit : P.toNat + len ≤ 2 ^ 32
  ctx : (ctxR s₀).Disjoint ⟨P.setWidth 64, len⟩
  stk : (stkR s₀).Disjoint ⟨P.setWidth 64, len⟩
  mem : (⟨P.setWidth 64, len⟩ : Region) ∈ s₀.rd ++ s₀.wr

theorem Src.bsrc {s₀ : State} {P : BitVec 32} {len : Nat} (hs : Src s₀ P len) {n : Nat} (hn : n ≤ len) :
    BSrc s₀ P n :=
  ⟨by have := hs.fit; omega, (hs.ctx.sub_left (sub_ctx s₀ (by omega))).sub_right (Region.sub_prefix hn),
   hs.stk.sub_right (Region.sub_prefix hn), ⟨_, hs.mem, 0, by simp, by simpa using hn⟩⟩

theorem shr4 (x : BitVec 32) : x >>> 4 = BitVec.ofNat 32 (x.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, toNat_ofNat32 (by have := x.isLt; omega)]

theorem and15 (x : BitVec 32) : x &&& 15 = BitVec.ofNat 32 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    toNat_ofNat32 (by omega)]

/-! ## The whole blocks -/

/-- Ready to call `vg_poly1305_blocks` for the whole blocks of the bytes whose
address and length are arguments `i` and `i + 1`. -/
structure MA (s₀ : State) (i : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  ebx : s.gpr .ebx = arg s₀ i
  ebp : s.gpr .ebp = arg s₀ (i + 1)
  eax : s.gpr .eax = BitVec.ofNat 32 ((arg s₀ (i + 1)).toNat / 16)
  ecx : s.gpr .ecx = C32 s₀ 448

theorem maA_ok {s₀ : State} (hp : APre s₀) {i : Nat} (hi : i + 1 < 5) {s : State} (h : Inv s₀ s) :
    WP isa (.block ([.mov .ebx (.mem (at_ .esp (4 + 4 * i))), .mov .ebp (.mem (at_ .esp (8 + 4 * i))),
      .mov .eax (.reg .ebp), .shift .shr .eax 4] ++ ptr .ecx .edi 448)) s fun s' =>
      MA s₀ i s' ∧ s'.mem = s.mem := by
  have i₁ : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by rw [h.rd, h.wr]; exact hp.in_arg (by omega)
  have i₂ : InRegions (s.rd ++ s.wr) (argAddr s₀ (i + 1)) 4 := by rw [h.rd, h.wr]; exact hp.in_arg hi
  have a₂ : argAddr s₀ (i + 1) = addr (E s₀) (8 + 4 * i) := by
    rw [argAddr_eq, show 4 + 4 * (i + 1) = 8 + 4 * i by omega]
  rw [List.cons_append]
  refine wp_movm (a := argAddr s₀ i) (by rw [ea_at, h.esp]; rfl) i₁ fun s₁ u₁ _ => ?_
  rw [List.cons_append]
  refine wp_movm (a := argAddr s₀ (i + 1)) (by rw [ea_at, u₁.other _ (by decide), h.esp, a₂])
    (by rw [u₁.rd, u₁.wr]; exact i₂) fun s₂ u₂ _ => ?_
  rw [List.cons_append]
  refine wp_mov fun s₃ u₃ _ => ?_
  rw [List.cons_append]
  refine wp_shr (by omega) fun s₄ u₄ => ?_
  refine WP.mono (ptr_ok .ecx .edi 448 s₄) fun s₅ ⟨e₅, g₅, rd₅, wr₅, m₅⟩ => ?_
  have mm : s₅.mem = s.mem := by rw [m₅, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have edi : s₄.gpr .edi = CX s₀ := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.edi]
  have ebp : s₂.gpr .ebp = arg s₀ (i + 1) := by rw [u₂.gpr, u₁.mem]; exact h.arg hp hi
  refine ⟨⟨h.step (by rw [g₅ _ (by decide), edi, h.edi])
      (by rw [g₅ _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide)])
      (by rw [rd₅, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [wr₅, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (rs := [])
      (by rw [mm]; exact Frame.refl _ _) (by simp) (by simp), ?_, ?_, ?_, by rw [e₅, edi]⟩, mm⟩
  · rw [g₅ _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    exact h.arg hp (by omega)
  · rw [g₅ _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), ebp]
  · rw [g₅ _ (by decide), u₄.gpr, u₃.gpr, ebp, shr4]

/-- After the whole blocks. -/
structure MB (s₀ : State) (i : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  ebx : s.gpr .ebx = arg s₀ i
  ebp : s.gpr .ebp = arg s₀ (i + 1)

theorem maB_ok {s₀ : State} (hp : APre s₀) {i : Nat} (hs : Src s₀ (arg s₀ i) (arg s₀ (i + 1)).toNat)
    {s : State} (h : MA s₀ i s) :
    WP isa (callWith [.eax, .ebx, .ecx] "vg_poly1305_blocks" Impl.Poly1305.X86.blocks) s fun s' =>
      MB s₀ i s' ∧ Frame [sub s₀ 448 128, stkR s₀] s.mem s'.mem ∧
      ∀ key msg, Repr s.mem (cx s₀ + BitVec.ofNat 64 448) key msg →
        Repr s'.mem (cx s₀ + BitVec.ofNat 64 448) key
          (msg ++ bytesAt s.mem ((arg s₀ i).setWidth 64) (16 * ((arg s₀ (i + 1)).toNat / 16))) :=
  blocks_call hp h.inv.at (by decide) (hs.bsrc (Nat.mul_div_le _ _)) h.ecx h.ebx h.eax
    fun s' at' cs' f' repr' =>
      ⟨⟨h.inv.part hp at' (cs' .edi (by simp [calleeSaved])) (k := 448) (n := 128) (by omega) (by omega)
        (by omega) f', by rw [cs' .ebx (by simp [calleeSaved]), h.ebx],
        by rw [cs' .ebp (by simp [calleeSaved]), h.ebp]⟩, f', repr'⟩

/-- The length of the tail tested. -/
structure MC (s₀ : State) (i : Nat) (s : State) : Prop extends MB s₀ i s where
  edx : s.gpr .edx = BitVec.ofNat 32 ((arg s₀ (i + 1)).toNat % 16)
  zf : s.zf = some (decide ((arg s₀ (i + 1)).toNat % 16 = 0))

set_option simprocs false in
theorem maC_ok {s₀ : State} {i : Nat} {s : State} (h : MB s₀ i s) :
    WP isa (.block [.mov .edx (.reg .ebp), .alu .and .edx (.imm 15)]) s fun s' =>
      MC s₀ i s' ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true]
  have e : s.gpr .ebp &&& 15 = BitVec.ofNat 32 ((arg s₀ (i + 1)).toNat % 16) := by rw [h.ebp, and15]
  refine ⟨⟨⟨h.inv.step (by simp (config := {decide := true})) (by simp (config := {decide := true})) rfl rfl
    (rs := []) (Frame.refl _ _) (by simp) (by simp), by simp (config := {decide := true}) [h.ebx],
    by simp (config := {decide := true}) [h.ebp]⟩, by simp; exact e, ?_⟩, trivial⟩
  simp only [e]
  by_cases h0 : (arg s₀ (i + 1)).toNat % 16 = 0
  · simp [h0]
  · have : BitVec.ofNat 32 ((arg s₀ (i + 1)).toNat % 16) ≠ 0 := by
      intro he; have := congrArg BitVec.toNat he; rw [toNat_ofNat32 (by omega)] at this; exact h0 this
    simp only [h0, decide_false, Option.some.injEq, beq_eq_false_iff_ne, ne_eq]
    exact this

/-! ## The tail, padded -/

/-- The zeroed block. -/
theorem zero16 (m : Mem) (c : Addr) {j : Nat} (hj : j < 16) :
    ((((m.writeW (c + BitVec.ofNat 64 576) (0 : BitVec 32)).writeW (c + BitVec.ofNat 64 580) (0 : BitVec 32)).writeW
      (c + BitVec.ofNat 64 584) (0 : BitVec 32)).writeW (c + BitVec.ofNat 64 588) (0 : BitVec 32))
        (c + BitVec.ofNat 64 (576 + j)) = 0 := by
  have key : ∀ d, d ≤ 12 → ((c + BitVec.ofNat 64 (576 + j) - (c + BitVec.ofNat 64 (576 + d))).toNat < 4 ↔
      d ≤ j ∧ j < d + 4) := by
    intro d hd
    rw [show c + BitVec.ofNat 64 (576 + j) - (c + BitVec.ofNat 64 (576 + d)) =
      BitVec.ofNat 64 (576 + j) - BitVec.ofNat 64 (576 + d) by bv_omega]
    constructor <;> intro h <;> bv_omega
  simp only [writeW32_zero_apply]
  rw [show (588 : Nat) = 576 + 12 from rfl, show (584 : Nat) = 576 + 8 from rfl,
    show (580 : Nat) = 576 + 4 from rfl, show c + BitVec.ofNat 64 576 = c + BitVec.ofNat 64 (576 + 0) from rfl]
  simp only [key 12 (by omega), key 8 (by omega), key 4 (by omega), key 0 (by omega)]
  split_ifs <;> first | rfl | omega

/-- The tail's start, its length in `edx`, and `ecx` at the zeroed block. -/
structure PD (s₀ : State) (i : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  esi : s.gpr .esi = arg s₀ i + BitVec.ofNat 32 (16 * ((arg s₀ (i + 1)).toNat / 16))
  ecx : s.gpr .ecx = C32 s₀ 576
  edx : s.gpr .edx = BitVec.ofNat 32 ((arg s₀ (i + 1)).toNat % 16)

theorem tail_start (P N : BitVec 32) :
    N - BitVec.ofNat 32 (N.toNat % 16) + P = P + BitVec.ofNat 32 (16 * (N.toNat / 16)) := by
  apply BitVec.eq_of_toNat_eq
  have := N.isLt
  have := P.isLt
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_sub_of_le (by
    rw [BitVec.le_def, toNat_ofNat32 (by omega)]; omega), toNat_ofNat32 (by omega), toNat_ofNat32 (by omega)]
  omega

theorem pd_ok {s₀ : State} (hp : APre s₀) {i : Nat} {s : State} (h : MC s₀ i s) :
    WP isa (.block ([.mov .esi (.reg .ebp), .alu .sub .esi (.reg .edx), .alu .add .esi (.reg .ebx),
      .mov .eax (.imm 0), .store (at_ .edi 576) .eax, .store (at_ .edi 580) .eax,
      .store (at_ .edi 584) .eax, .store (at_ .edi 588) .eax] ++ ptr .ecx .edi 576)) s fun s' =>
      PD s₀ i s' ∧ Frame [sub s₀ 576 16] s.mem s'.mem ∧
      ∀ j < 16, s'.mem (cx s₀ + BitVec.ofNat 64 (576 + j)) = 0 := by
  have hi := h.inv
  have o : ∀ d, d + 4 ≤ 1024 → InRegions s.wr (cx s₀ + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [hi.wr]; exact hp.in_ctx hd
  simp only [List.cons_append]
  refine wp_mov fun s₁ u₁ _ => wp_subx (readSrc_reg _ _) fun s₂ u₂ _ =>
    wp_addx (readSrc_reg _ _) fun s₃ u₃ _ => wp_movi fun s₄ u₄ _ => ?_
  have edi₄ : s₄.gpr .edi = CX s₀ := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hi.edi]
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have c : ∀ d, d < 1024 → ∀ s' : State, s'.gpr .edi = CX s₀ → s'.ea (at_ .edi d) = cx s₀ + BitVec.ofNat 64 d :=
    fun d hd s' he => by rw [ea_at, he, hp.ea_ctx hd]
  refine wp_store (c 576 (by omega) _ edi₄) (by rw [wr₄]; exact o 576 (by omega)) fun s₅ u₅ => ?_
  refine wp_store (c 580 (by omega) _ (by rw [u₅.gpr, edi₄])) (by rw [u₅.wr, wr₄]; exact o 580 (by omega))
    fun s₆ u₆ => ?_
  refine wp_store (c 584 (by omega) _ (by rw [u₆.gpr, u₅.gpr, edi₄]))
    (by rw [u₆.wr, u₅.wr, wr₄]; exact o 584 (by omega)) fun s₇ u₇ => ?_
  refine wp_store (c 588 (by omega) _ (by rw [u₇.gpr, u₆.gpr, u₅.gpr, edi₄]))
    (by rw [u₇.wr, u₆.wr, u₅.wr, wr₄]; exact o 588 (by omega)) fun s₈ u₈ => ?_
  refine WP.mono (ptr_ok .ecx .edi 576 s₈) fun s₉ ⟨e₉, g₉, rd₉, wr₉, m₉⟩ => ?_
  have g8 : s₈.gpr = s₄.gpr := by rw [u₈.gpr, u₇.gpr, u₆.gpr, u₅.gpr]
  have eax₄ : s₄.gpr .eax = 0 := u₄.gpr
  have hm : s₉.mem = (((s.mem.writeW (cx s₀ + BitVec.ofNat 64 576) (0 : BitVec 32)).writeW
      (cx s₀ + BitVec.ofNat 64 580) (0 : BitVec 32)).writeW (cx s₀ + BitVec.ofNat 64 584) (0 : BitVec 32)).writeW
      (cx s₀ + BitVec.ofNat 64 588) (0 : BitVec 32) := by
    rw [m₉, u₈.mem, u₇.gpr, u₇.mem, u₆.gpr, u₆.mem, u₅.gpr, u₅.mem, eax₄, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hf : Frame [sub s₀ 576 16] s.mem s₉.mem := by
    rw [hm]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub s₀ le_rfl (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (contains_sub s₀ (by omega) (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (contains_sub s₀ (by omega) (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (contains_sub s₀ (by omega) (by omega) (by omega))
  have g9 : ∀ r, r ≠ .ecx → s₉.gpr r = s₄.gpr r := fun r hr => by rw [g₉ r hr, g8]
  refine ⟨⟨hi.part hp ⟨by rw [g9 _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hi.esp], by rw [rd₉, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd,
      u₃.rd, u₂.rd, u₁.rd, hi.rd], by rw [wr₉, u₈.wr, u₇.wr, u₆.wr, u₅.wr, wr₄, hi.wr]⟩
      (by rw [g9 _ (by decide), edi₄, hi.edi]) (k := 576) (n := 16) (by omega) (by omega) (by omega)
      (hf.mono (by simp)), ?_, by rw [e₉, g8, edi₄], ?_⟩, hf, fun j hj => by rw [hm]; exact zero16 _ _ hj⟩
  · rw [g9 _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), u₁.other _ (by decide), h.ebp, h.edx, h.ebx, tail_start]
  · rw [g9 _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.edx]

/-! ## Copying the tail -/

/-- The `t` bytes at `Q` that the copy loop copies. -/
structure Tail (s₀ : State) (Q : BitVec 32) (t : Nat) : Prop where
  lt : t < 16
  fit : Q.toNat + t ≤ 2 ^ 32
  src : ∀ j < t, InRegions (s₀.rd ++ s₀.wr) (Q.setWidth 64 + BitVec.ofNat 64 j) 1
  disj : (⟨Q.setWidth 64, t⟩ : Region).Disjoint (sub s₀ 576 16)

/-- Before byte `i` of the tail is copied into the block, from the state `s₂`
in which the block was zeroed. -/
structure CpInv (s₀ s₂ : State) (Q : BitVec 32) (t i : Nat) (s : State) : Prop where
  esi : s.gpr .esi = Q + BitVec.ofNat 32 i
  ecx : s.gpr .ecx = C32 s₀ (576 + i)
  edx : s.gpr .edx = BitVec.ofNat 32 (t - i)
  keep : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ecx → r ≠ .edx → s.gpr r = s₂.gpr r
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame [sub s₀ 576 16] s₂.mem s.mem
  buf : ∀ j < 16, s.mem (cx s₀ + BitVec.ofNat 64 (576 + j)) =
    if j < i then s₂.mem (Q.setWidth 64 + BitVec.ofNat 64 j) else 0

def copyBody : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .store8 (at_ .ecx 0) .al, .alu .add .esi (.imm 1), .alu .add .ecx (.imm 1),
    .alu .sub .edx (.imm 1)]

theorem ctx_ne {s₀ : State} {j k : Nat} (hj : j < 16) (hk : k < 16) (h : j ≠ k) :
    cx s₀ + BitVec.ofNat 64 (576 + j) ≠ cx s₀ + BitVec.ofNat 64 (576 + k) := by
  intro he
  have e : BitVec.ofNat 64 (576 + j) = BitVec.ofNat 64 (576 + k) := by
    have := congrArg (· - cx s₀) he; simpa using this
  have := congrArg BitVec.toNat e
  rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at this
  omega

theorem copy_step {s₀ : State} (hp : APre s₀) {s₂ : State} (hr₂ : s₂.rd = s₀.rd) (hw₂ : s₂.wr = s₀.wr)
    {Q : BitVec 32} {t : Nat} (ht : Tail s₀ Q t) {i : Nat} (hi : i < t) {s : State}
    (h : CpInv s₀ s₂ Q t i s) :
    WP isa (.block copyBody) s fun s' => CpInv s₀ s₂ Q t (i + 1) s' ∧ s'.zf = some (decide (i + 1 = t)) := by
  have hlt := ht.lt
  have hf := ht.fit
  have hc := hp.fit_c
  have hQ : addr (Q + BitVec.ofNat 32 i) 0 = Q.setWidth 64 + BitVec.ofNat 64 i := by
    rw [addr_zero_add, addr_eq (by omega)]
  have hO : addr (C32 s₀ (576 + i)) 0 = cx s₀ + BitVec.ofNat 64 (576 + i) := by
    rw [show C32 s₀ (576 + i) = CX s₀ + BitVec.ofNat 32 (576 + i) from rfl, addr_zero_add, hp.ea_ctx (by omega)]
  refine wp_movzx8 (a := Q.setWidth 64 + BitVec.ofNat 64 i) (by rw [ea_at, h.esi, hQ])
    (by rw [h.rd, h.wr, hr₂, hw₂]; exact ht.src i hi) fun s₃ u₃ => ?_
  refine wp_store8 (a := cx s₀ + BitVec.ofNat 64 (576 + i)) (by rw [ea_at, u₃.other _ (by decide), h.ecx, hO])
    (by rw [u₃.wr, h.wr, hw₂]; exact hp.in_ctx (by omega)) fun s₄ u₄ => ?_
  refine wp_addx (readSrc_imm _ _) fun s₅ u₅ _ => wp_addx (readSrc_imm _ _) fun s₆ u₆ _ =>
    wp_subx (readSrc_imm _ _) fun s₇ u₇ z₇ => WP.block_nil ?_
  -- The byte copied is byte `i` of the tail, unchanged since `s₂`.
  have hbyte : s.mem (Q.setWidth 64 + BitVec.ofNat 64 i) = s₂.mem (Q.setWidth 64 + BitVec.ofNat 64 i) :=
    h.frame.bytes (R := ⟨Q.setWidth 64, t⟩) (by simp only [List.mem_singleton, forall_eq]; exact ht.disj)
      (show t ≤ 2 ^ 64 by omega) hi
  have hmem : s₇.mem = s.mem.writeW (cx s₀ + BitVec.ofNat 64 (576 + i))
      (s₂.mem (Q.setWidth 64 + BitVec.ofNat 64 i)) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, show Reg8.al.reg = .eax from rfl, u₃.gpr, u₃.mem,
      BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq, hbyte]
  have hedx : s.gpr .edx - 1 = BitVec.ofNat 32 (t - (i + 1)) := by
    rw [h.edx]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_ofNat32 (by omega)]; simp; omega),
      toNat_ofNat32 (by omega), toNat_ofNat32 (by omega)]
    simp; omega
  refine ⟨⟨?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, h.rd],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, h.wr], ?_, fun k hk => ?_⟩, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide), h.esi,
      add_ofNat_one]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), h.ecx]
    show CX s₀ + BitVec.ofNat 32 (576 + i) + 1 = CX s₀ + BitVec.ofNat 32 (576 + i + 1)
    rw [add_ofNat_one]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), hedx]
  · rw [u₇.other _ h₄, u₆.other _ h₃, u₅.other _ h₂, u₄.gpr, u₃.other _ h₁, h.keep r h₁ h₂ h₃ h₄]
  · rw [hmem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by omega) (by omega) (by omega))
  · rw [hmem, writeW8_apply]
    by_cases hki : k = i
    · subst hki
      rw [ite_eq_left rfl, ite_eq_left (by omega)]
    · rw [ite_eq_right (ctx_ne hk (by omega) hki), h.buf k hk]
      rcases Nat.lt_or_ge k i with hk' | hk'
      · rw [ite_eq_left hk', ite_eq_left (by omega)]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [z₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), hedx]
    refine congrArg some ?_
    by_cases he : i + 1 = t
    · rw [decide_eq_true he, show t - (i + 1) = 0 by omega]; rfl
    · rw [decide_eq_false he]
      refine beq_eq_false_iff_ne.mpr fun h0 => ?_
      have := congrArg BitVec.toNat h0
      rw [toNat_ofNat32 (by omega)] at this
      simp at this; omega

theorem copyLoop_eq : (Code.loop (.block [.movzx8 .eax (at_ .esi 0), .store8 (at_ .ecx 0) .al,
    .alu .add .esi (.imm 1), .alu .add .ecx (.imm 1), .alu .sub .edx (.imm 1)]) .ne : Prog isa) =
    .loop (.block copyBody) .ne := rfl

theorem copy_ok {s₀ : State} (hp : APre s₀) {s₂ : State} (hr₂ : s₂.rd = s₀.rd) (hw₂ : s₂.wr = s₀.wr)
    {Q : BitVec 32} {t : Nat} (ht : Tail s₀ Q t) (ht0 : 0 < t) (h₂ : CpInv s₀ s₂ Q t 0 s₂) :
    WP isa (.loop (.block copyBody) .ne) s₂ (CpInv s₀ s₂ Q t t) := by
  let Inv : Nat → State → Prop := fun n s => ∃ i, n = t - i ∧ i < t ∧ CpInv s₀ s₂ Q t i s
  have hstep : ∀ n s, Inv n s → WP isa (.block copyBody) s (fun s' =>
      (eval .ne s' = some false ∧ CpInv s₀ s₂ Q t t s') ∨ (eval .ne s' = some true ∧ ∃ n' < n, Inv n' s')) := by
    rintro n s ⟨i, rfl, hi, hI⟩
    refine WP.mono (copy_step hp hr₂ hw₂ ht hi hI) fun s' ⟨h', hz⟩ => ?_
    by_cases hl : i + 1 = t
    · exact .inl ⟨by simp [eval, hz, hl], hl ▸ h'⟩
    · exact .inr ⟨by simp [eval, hz, hl], t - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep t s₂ ⟨0, by simp, ht0, h₂⟩

/-- The padded block's bytes. -/
theorem padded_bytes {s₀ : State} {m mz : Mem} {Q : Addr} {t : Nat} (ht : t < 16)
    (h : ∀ j < 16, m (cx s₀ + BitVec.ofNat 64 (576 + j)) = if j < t then mz (Q + BitVec.ofNat 64 j) else 0) :
    bytesAt m (cx s₀ + BitVec.ofNat 64 576) 16 = bytesAt mz Q t ++ List.replicate (16 - t) 0 := by
  apply List.ext_getElem
  · simp [bytesAt]; omega
  · intro k h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [show cx s₀ + BitVec.ofNat 64 576 + BitVec.ofNat 64 k = cx s₀ + BitVec.ofNat 64 (576 + k) by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add], h k h₁]
    by_cases hk : k < t
    · rw [List.getElem_append_left (by simp [hk])]
      simp [hk]
    · rw [List.getElem_append_right (by simp; omega)]
      simp [hk]

/-! ## The tail absorbed -/

/-- The frame of the Poly1305 state and the padded block, and the calls. -/
abbrev macR (s₀ : State) : List Region := [sub s₀ 448 144, stkR s₀]

theorem Src.tail {s₀ : State} {P : BitVec 32} {len : Nat} (hs : Src s₀ P len) :
    Tail s₀ (P + BitVec.ofNat 32 (16 * (len / 16))) (len % 16) := by
  have hf := hs.fit
  have hk : 16 * (len / 16) + len % 16 = len := Nat.div_add_mod _ _
  by_cases h0 : len % 16 = 0
  · rw [h0]
    refine ⟨by omega, by have := (P + BitVec.ofNat 32 (16 * (len / 16))).isLt; omega,
      fun j hj => absurd hj (by omega), fun x hx _ => ?_⟩
    simp only [Region.Contains] at hx; omega
  have e : (P + BitVec.ofNat 32 (16 * (len / 16))).setWidth 64 =
      P.setWidth 64 + BitVec.ofNat 64 (16 * (len / 16)) := add_setWidth (by omega)
  have hsub : ∀ {a n : Nat}, a + n ≤ len % 16 →
      Region.Sub ⟨(P + BitVec.ofNat 32 (16 * (len / 16))).setWidth 64 + BitVec.ofNat 64 a, n⟩
        ⟨P.setWidth 64, len⟩ := fun {a n} h => by
    rw [e, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact sub_off _ (by omega)
  refine ⟨Nat.mod_lt _ (by omega), by rw [add_toNat (by omega)]; omega, fun j hj => ?_, ?_⟩
  · exact ⟨_, hs.mem, hsub (a := j) (n := 1) (by omega) _ (Region.contains_self _ _)⟩
  · have hd := (hs.ctx.sub_left (sub_ctx s₀ (k := 576) (n := 16) (by omega))).symm
    refine hd.sub_left ?_
    have := hsub (a := 0) (n := len % 16) (by omega)
    simpa using this

theorem padTail_eq : padTail =
    .seq (.block ([.mov .esi (.reg .ebp), .alu .sub .esi (.reg .edx), .alu .add .esi (.reg .ebx),
      .mov .eax (.imm 0), .store (at_ .edi 576) .eax, .store (at_ .edi 580) .eax,
      .store (at_ .edi 584) .eax, .store (at_ .edi 588) .eax] ++ ptr .ecx .edi 576))
    (.seq (.loop (.block copyBody) .ne) (absorbOne 576)) := rfl

/-- After the copy loop. -/
theorem copied_inv {s₀ : State} (hp : APre s₀) {i : Nat} {s₂ s₃ : State} (h₂ : PD s₀ i s₂)
    {Q : BitVec 32} {t : Nat} (h₃ : CpInv s₀ s₂ Q t t s₃) : Inv s₀ s₃ :=
  h₂.inv.part hp ⟨by rw [h₃.keep _ (by decide) (by decide) (by decide) (by decide), h₂.inv.esp],
    by rw [h₃.rd, h₂.inv.rd], by rw [h₃.wr, h₂.inv.wr]⟩
    (h₃.keep _ (by decide) (by decide) (by decide) (by decide)) (k := 576) (n := 16) (by omega) (by omega)
    (by omega) (h₃.frame.mono (by simp))

theorem cp0 {s₀ : State} {i : Nat} {s₂ : State} (h₂ : PD s₀ i s₂)
    (hz : ∀ j < 16, s₂.mem (cx s₀ + BitVec.ofNat 64 (576 + j)) = 0) :
    CpInv s₀ s₂ (arg s₀ i + BitVec.ofNat 32 (16 * ((arg s₀ (i + 1)).toNat / 16)))
      ((arg s₀ (i + 1)).toNat % 16) 0 s₂ :=
  ⟨by rw [h₂.esi]; simp, h₂.ecx, by rw [h₂.edx]; rfl, fun _ _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _,
    fun j hj => by rw [hz j hj]; simp⟩

theorem padTail_ok {s₀ : State} (hp : APre s₀) {i : Nat} (hs : Src s₀ (arg s₀ i) (arg s₀ (i + 1)).toNat)
    (h0 : (arg s₀ (i + 1)).toNat % 16 ≠ 0) {s : State} (h : MC s₀ i s) :
    WP isa padTail s fun s' => Inv s₀ s' ∧ Frame (macR s₀) s.mem s'.mem ∧
      ∀ key msg, Repr s.mem (cx s₀ + BitVec.ofNat 64 448) key msg →
        Repr s'.mem (cx s₀ + BitVec.ofNat 64 448) key (msg ++
          (bytesAt s.mem ((arg s₀ i + BitVec.ofNat 32 (16 * ((arg s₀ (i + 1)).toNat / 16))).setWidth 64)
            ((arg s₀ (i + 1)).toNat % 16) ++ List.replicate (16 - (arg s₀ (i + 1)).toNat % 16) 0)) := by
  have ht := hs.tail
  rw [padTail_eq]
  refine WP.seq (WP.mono (pd_ok hp h) fun s₂ ⟨h₂, f₂, z₂⟩ => ?_)
  refine WP.seq (WP.mono (copy_ok hp (by rw [h₂.inv.rd]) (by rw [h₂.inv.wr]) ht (by omega) (cp0 h₂ z₂))
    fun s₃ h₃ => ?_)
  refine WP.mono (absorbOne_ok hp (copied_inv hp h₂ h₃) (k := 576) (.inr ⟨le_rfl, by omega⟩))
    fun s₄ ⟨i₄, f₄, r₄⟩ => ⟨i₄, ?_, fun key msg hr => ?_⟩
  · refine ((f₂.trans h₃.frame).sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨sub s₀ 448 144, by simp, sub_sub s₀ (by omega) (by omega) (by omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨sub s₀ 448 144, by simp, sub_sub s₀ le_rfl (by omega) (by omega)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · have f23 : Frame [sub s₀ 576 16] s.mem s₃.mem := f₂.trans h₃.frame
    have := r₄ key msg (Repr.frame f23 (by
      simp only [List.mem_singleton, forall_eq]; exact sub_disj s₀ (by omega) (by omega) (by omega)) hr)
    rwa [padded_bytes ht.lt h₃.buf, bytesAt_frame f₂ (by
      simp only [List.mem_singleton, forall_eq]; exact ht.disj) (by have := ht.lt; omega)] at this

theorem macPad_eq (p n : Nat) : macPad p n =
    .seq (.block ([.mov .ebx (.mem (at_ .esp p)), .mov .ebp (.mem (at_ .esp n)), .mov .eax (.reg .ebp),
      .shift .shr .eax 4] ++ ptr .ecx .edi 448))
    (.seq (callWith [.eax, .ebx, .ecx] "vg_poly1305_blocks" Impl.Poly1305.X86.blocks)
    (.seq (.block [.mov .edx (.reg .ebp), .alu .and .edx (.imm 15)])
      (.ite .e (.block []) padTail))) := rfl

/-- The bytes whose address and length are arguments `i` and `i + 1`, padded
with zeros, absorbed. -/
theorem macPad_ok {s₀ : State} (hp : APre s₀) {i : Nat} (hi : i + 1 < 5)
    (hs : Src s₀ (arg s₀ i) (arg s₀ (i + 1)).toNat) {s : State} (h : Inv s₀ s) :
    WP isa (macPad (4 + 4 * i) (8 + 4 * i)) s fun s' => Inv s₀ s' ∧ Frame (macR s₀) s.mem s'.mem ∧
      ∀ key msg, Repr s.mem (cx s₀ + BitVec.ofNat 64 448) key msg →
        Repr s'.mem (cx s₀ + BitVec.ofNat 64 448) key (msg ++
          (bytesAt s.mem ((arg s₀ i).setWidth 64) (arg s₀ (i + 1)).toNat ++
            pad16 (bytesAt s.mem ((arg s₀ i).setWidth 64) (arg s₀ (i + 1)).toNat))) := by
  have hf := hs.fit
  rw [macPad_eq]
  refine WP.seq (WP.mono (maA_ok hp hi h) fun s₁ ⟨h₁, m₁⟩ => ?_)
  refine WP.seq (WP.mono (maB_ok hp hs h₁) fun s₂ ⟨h₂, f₂, r₂⟩ => ?_)
  rw [m₁] at f₂ r₂
  refine WP.seq (WP.mono (maC_ok h₂) fun s₃ ⟨h₃, m₃⟩ => ?_)
  have hk : 16 * ((arg s₀ (i + 1)).toNat / 16) + (arg s₀ (i + 1)).toNat % 16 = (arg s₀ (i + 1)).toNat := Nat.div_add_mod _ _
  have fr₃ : Frame (macR s₀) s.mem s₃.mem := by
    rw [m₃]
    exact f₂.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨sub s₀ 448 144, by simp, sub_sub s₀ le_rfl (by omega) (by omega)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  have x_eq : bytesAt s.mem ((arg s₀ i).setWidth 64) (arg s₀ (i + 1)).toNat = bytesAt s.mem ((arg s₀ i).setWidth 64) (16 * ((arg s₀ (i + 1)).toNat / 16)) ++
      bytesAt s.mem ((arg s₀ i).setWidth 64 + BitVec.ofNat 64 (16 * ((arg s₀ (i + 1)).toNat / 16))) ((arg s₀ (i + 1)).toNat % 16) := by
    rw [← VG.Proof.Poly1305.bytesAt_add, hk]
  have hlenX : (bytesAt s.mem ((arg s₀ i).setWidth 64) (arg s₀ (i + 1)).toNat).length = (arg s₀ (i + 1)).toNat := VG.Proof.Poly1305.length_bytesAt _ _ _
  refine WP.ite (decide ((arg s₀ (i + 1)).toNat % 16 = 0)) (by simp only [eval, h₃.zf]) (fun hz => ?_) (fun hz => ?_)
  · have h0 : (arg s₀ (i + 1)).toNat % 16 = 0 := by simpa using hz
    refine WP.block_nil ⟨h₃.inv, fr₃, fun key msg hr => ?_⟩
    rw [m₃]
    have := r₂ key msg hr
    rwa [show pad16 (bytesAt s.mem ((arg s₀ i).setWidth 64) (arg s₀ (i + 1)).toNat) = [] by simp [pad16, hlenX, h0],
      List.append_nil, ← show 16 * ((arg s₀ (i + 1)).toNat / 16) = (arg s₀ (i + 1)).toNat by omega]
  · have h0 : (arg s₀ (i + 1)).toNat % 16 ≠ 0 := by simpa using hz
    refine WP.mono (padTail_ok hp (i := i) hs h0 h₃) fun s₄ ⟨i₄, f₄, r₄⟩ => ⟨i₄, fr₃.trans f₄, fun key msg hr => ?_⟩
    have := r₄ key _ (by rw [m₃]; exact r₂ key msg hr)
    have e : (arg s₀ i + BitVec.ofNat 32 (16 * ((arg s₀ (i + 1)).toNat / 16))).setWidth 64 =
        (arg s₀ i).setWidth 64 + BitVec.ofNat 64 (16 * ((arg s₀ (i + 1)).toNat / 16)) := add_setWidth (by omega)
    rw [e, m₃, bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ((hs.ctx.sub_left (sub_ctx s₀ (k := 448) (n := 128) (by omega))).symm).sub_left
          (sub_off _ (by omega))
      · exact (hs.stk.symm).sub_left (sub_off _ (by omega))) (by omega)] at this
    rw [show pad16 (bytesAt s.mem ((arg s₀ i).setWidth 64) (arg s₀ (i + 1)).toNat) = List.replicate (16 - (arg s₀ (i + 1)).toNat % 16) 0 by
      simp [pad16, hlenX, h0], x_eq]
    simpa only [List.append_assoc] using this

end VG.Proof.ChaCha20Poly1305.X86
