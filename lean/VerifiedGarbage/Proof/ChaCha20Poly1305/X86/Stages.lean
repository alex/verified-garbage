import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.MacPad
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.Prologue

/-!
# ChaCha20-Poly1305 on x86 (32-bit): the other parts

Untrusted: everything here is checked by Lean. The lengths block, the
encryption, the tag, comparing tags, and restoring the registers.
-/

namespace VG.Proof.ChaCha20Poly1305.X86

open VG VG.X86 VG.Impl.ChaCha20Poly1305.X86
open VG.Impl.ChaCha20.X86 (at_)
open VG.Proof.ChaCha20.X86 (contains_off toNat_ofNat_lt readW_writeW_off)
open VG.Proof.Poly1305.X86 (wp_movm wp_store wp_movi wp_mov Upd Mupd leNum_bytesAt_4)
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt keystream)

/-! ## The lengths block -/

theorem bytesAt_word (m : Mem) (p : Addr) : bytesAt m p 4 = leBytes 4 (m.readW p 32).toNat := by
  rw [VG.Proof.Poly1305.bytesAt_leBytes]; simp [Mem.readW]

/-- Eight bytes, a word and a zero word. -/
theorem bytesAt_len (m : Mem) (p : Addr) (h : m.readW (p + BitVec.ofNat 64 4) 32 = 0) :
    bytesAt m p 8 = leBytes 8 (m.readW p 32).toNat := by
  rw [show (8 : Nat) = 4 + 4 from rfl, VG.Proof.Poly1305.bytesAt_add, bytesAt_word, bytesAt_word, h,
    VG.Proof.Poly1305.leBytes_add, Nat.div_eq_of_lt (by have := (m.readW p 32).isLt; omega)]
  rfl

theorem lengths_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block lengths) s fun s' => Inv s₀ s' ∧ Frame [sub s₀ 656 16] s.mem s'.mem ∧
      bytesAt s'.mem (cx s₀ + BitVec.ofNat 64 656) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
  have o : ∀ d, d + 4 ≤ 1024 → InRegions s.wr (cx s₀ + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [h.wr]; exact hp.in_ctx hd
  have c : ∀ d, d < 1024 → ∀ s' : State, s'.gpr .edi = CX s₀ → s'.ea (at_ .edi d) = cx s₀ + BitVec.ofNat 64 d :=
    fun d hd s' he => by rw [ea_at, he, hp.ea_ctx hd]
  have i₂ : InRegions (s.rd ++ s.wr) (argAddr s₀ 2) 4 := by rw [h.rd, h.wr]; exact hp.in_arg (by omega)
  have i₄ : InRegions (s.rd ++ s.wr) (argAddr s₀ 4) 4 := by rw [h.rd, h.wr]; exact hp.in_arg (by omega)
  refine wp_movm (a := argAddr s₀ 2) (by rw [ea_at, h.esp]; rfl) i₂ fun s₁ u₁ _ => ?_
  refine wp_store (c 656 (by omega) _ (by rw [u₁.other _ (by decide), h.edi]))
    (by rw [u₁.wr]; exact o 656 (by omega)) fun s₂ u₂ => ?_
  refine wp_movm (a := argAddr s₀ 4) (by rw [ea_at, u₂.gpr, u₁.other _ (by decide), h.esp]; rfl)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact i₄) fun s₃ u₃ _ => ?_
  refine wp_store (c 664 (by omega) _ (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.edi]))
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact o 664 (by omega)) fun s₄ u₄ => ?_
  refine wp_movi fun s₅ u₅ _ => ?_
  have edi₅ : s₅.gpr .edi = CX s₀ := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.edi]
  refine wp_store (c 660 (by omega) _ edi₅) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact o 660 (by omega))
    fun s₆ u₆ => ?_
  refine wp_store (c 668 (by omega) _ (by rw [u₆.gpr, edi₅]))
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact o 668 (by omega)) fun s₇ u₇ => WP.block_nil ?_
  have v₁ : s₁.gpr .eax = ALN s₀ := by rw [u₁.gpr]; exact h.arg hp (by omega)
  have v₃ : s₃.gpr .eax = LN s₀ := by
    rw [u₃.gpr, u₂.mem, u₁.mem, Mem.readW_writeW_sep ((hp.g_sub (k := 656) (n := 4) (by omega)).sep
      (hp.arg_contains (by omega)) (Region.contains_self _ _)) (by decide)]
    exact h.arg hp (by omega)
  have hm : s₇.mem = (((s.mem.writeW (cx s₀ + BitVec.ofNat 64 656) (ALN s₀)).writeW (cx s₀ + BitVec.ofNat 64 664)
      (LN s₀)).writeW (cx s₀ + BitVec.ofNat 64 660) (0 : BitVec 32)).writeW (cx s₀ + BitVec.ofNat 64 668)
      (0 : BitVec 32) := by
    rw [u₇.mem, u₆.gpr, u₆.mem, u₅.gpr, u₅.mem, u₄.mem, v₃, u₃.mem, u₂.mem, v₁, u₁.mem]
  have hf : Frame [sub s₀ 656 16] s.mem s₇.mem := by
    rw [hm]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub s₀ le_rfl (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (contains_sub s₀ (by omega) (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (contains_sub s₀ (by omega) (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (contains_sub s₀ (by omega) (by omega) (by omega))
  refine ⟨h.part hp ⟨by rw [u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), h.esp], by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
      by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]⟩ (by rw [u₇.gpr, u₆.gpr, edi₅, h.edi])
      (k := 656) (n := 16) (by omega) (by omega) (by omega) (hf.mono (by simp)), hf, ?_⟩
  have e : ∀ a b : Nat, cx s₀ + BitVec.ofNat 64 a + BitVec.ofNat 64 b = cx s₀ + BitVec.ofNat 64 (a + b) :=
    fun a b => by rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [show (16 : Nat) = 8 + 8 from rfl, VG.Proof.Poly1305.bytesAt_add, e, bytesAt_len _ _ (by rw [e, hm]; simp
    [readW_writeW_off _ _ _ (show 656 + 4 < 2 ^ 32 by omega) (show 668 < 2 ^ 32 by omega) (by omega),
      Mem.readW_writeW_self32]), bytesAt_len _ _ (by rw [e, hm]; simp
    [Mem.readW_writeW_self32])]
  rw [hm, readW_writeW_off _ _ _ (show 656 + 8 < 2 ^ 32 by omega) (show 668 < 2 ^ 32 by omega) (by omega),
    readW_writeW_off _ _ _ (show 656 + 8 < 2 ^ 32 by omega) (show 660 < 2 ^ 32 by omega) (by omega),
    Mem.readW_writeW_self32, readW_writeW_off _ _ _ (show 656 < 2 ^ 32 by omega) (show 668 < 2 ^ 32 by omega) (by omega),
    readW_writeW_off _ _ _ (show 656 < 2 ^ 32 by omega) (show 660 < 2 ^ 32 by omega) (by omega),
    readW_writeW_off _ _ _ (show 656 < 2 ^ 32 by omega) (show 664 < 2 ^ 32 by omega) (by omega),
    Mem.readW_writeW_self32]

/-! ## Encrypting -/

theorem set12_initState (key nonce : List Byte) :
    (Spec.ChaCha20.initState key 0 nonce).set 12 1 = Spec.ChaCha20.initState key 1 nonce := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_set, Spec.ChaCha20.initState, Vector.getElem_ofFn]
  by_cases h : 12 = i
  · subst h; simp
  · simp only [h, ite_false, show ¬ i = 12 from fun h' => h h'.symm]

/-- Setting the block counter in memory. -/
theorem stateAt_ctr (m : Mem) (c : Addr) :
    stateAt (m.writeW (c + BitVec.ofNat 64 112) (1 : BitVec 32)) (c + BitVec.ofNat 64 64) =
      (stateAt m (c + BitVec.ofNat 64 64)).set 12 1 := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_set, Vector.getElem_ofFn]
  rw [show c + BitVec.ofNat 64 64 + BitVec.ofNat 64 (4 * i) = c + BitVec.ofNat 64 (64 + 4 * i) by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
  by_cases h : 12 = i
  · subst h; simp only [ite_true]; exact Mem.readW_writeW_self32 _ _ _
  · simp only [h, ite_false]
    exact readW_writeW_off m c 1 (by omega) (by omega) (by omega)

/-- Ready to call `vg_chacha20_xor`. -/
structure CrA (s₀ s : State) : Prop where
  inv : Inv s₀ s
  eax : s.gpr .eax = C32 s₀ 64
  ecx : s.gpr .ecx = DP s₀
  edx : s.gpr .edx = LN s₀
  esi : s.gpr .esi = C32 s₀ 128

theorem crA_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block ([.mov .eax (.imm 1), .store (at_ .edi 112) .eax] ++ ptr .eax .edi 64 ++
      [.mov .ecx (.mem (at_ .esp 16)), .mov .edx (.mem (at_ .esp 20))] ++ ptr .esi .edi 128)) s fun s' =>
      CrA s₀ s' ∧ s'.mem = s.mem.writeW (cx s₀ + BitVec.ofNat 64 112) (1 : BitVec 32) := by
  rw [show ([.mov .eax (.imm 1), .store (at_ .edi 112) .eax] ++ ptr .eax .edi 64 ++
      [.mov .ecx (.mem (at_ .esp 16)), .mov .edx (.mem (at_ .esp 20))] ++ ptr .esi .edi 128 : List Instr) =
    .mov .eax (.imm 1) :: .store (at_ .edi 112) .eax :: (ptr .eax .edi 64 ++
      (.mov .ecx (.mem (at_ .esp 16)) :: .mov .edx (.mem (at_ .esp 20)) :: ptr .esi .edi 128)) from rfl]
  refine wp_movi fun s₁ u₁ _ => ?_
  refine wp_store (a := cx s₀ + BitVec.ofNat 64 112) (by rw [ea_at, u₁.other _ (by decide), h.edi,
    hp.ea_ctx (by omega)]) (by rw [u₁.wr, h.wr]; exact hp.in_ctx (by omega)) fun s₂ u₂ => ?_
  have hm₂ : s₂.mem = s.mem.writeW (cx s₀ + BitVec.ofNat 64 112) (1 : BitVec 32) := by
    rw [u₂.mem, u₁.gpr, u₁.mem]
  have edi₂ : s₂.gpr .edi = CX s₀ := by rw [u₂.gpr, u₁.other _ (by decide), h.edi]
  have hf₂ : Frame [sub s₀ 112 4, stkR s₀] s.mem s₂.mem := by
    rw [hm₂]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _ (contains_sub s₀ le_rfl (by omega) (by omega))
  have inv₂ : Inv s₀ s₂ := h.part hp ⟨by rw [u₂.gpr, u₁.other _ (by decide), h.esp],
    by rw [u₂.rd, u₁.rd, h.rd], by rw [u₂.wr, u₁.wr, h.wr]⟩ (by rw [edi₂, h.edi]) (by omega) (by omega)
    (by omega) hf₂
  refine WP.block_append (WP.mono (ptr_ok .eax .edi 64 s₂) fun s₃ ⟨e₃, g₃, rd₃, wr₃, m₃⟩ => ?_)
  have esp₃ : s₃.gpr .esp = E s₀ := by rw [g₃ _ (by decide), inv₂.esp]
  have in₃ : ∀ i, i < 5 → InRegions (s₃.rd ++ s₃.wr) (argAddr s₀ i) 4 := fun i hi => by
    rw [rd₃, wr₃, inv₂.rd, inv₂.wr]; exact hp.in_arg hi
  refine wp_movm (a := argAddr s₀ 3) (by rw [ea_at, esp₃]; rfl) (in₃ 3 (by omega)) fun s₄ u₄ _ => ?_
  refine wp_movm (a := argAddr s₀ 4) (by rw [ea_at, u₄.other _ (by decide), esp₃]; rfl)
    (by rw [u₄.rd, u₄.wr]; exact in₃ 4 (by omega)) fun s₅ u₅ _ => ?_
  refine WP.mono (ptr_ok .esi .edi 128 s₅) fun s₆ ⟨e₆, g₆, rd₆, wr₆, m₆⟩ => ?_
  have edi₅ : s₅.gpr .edi = CX s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), edi₂]
  have mm : s₆.mem = s₂.mem := by rw [m₆, u₅.mem, u₄.mem, m₃]
  refine ⟨⟨inv₂.step (by rw [g₆ _ (by decide), edi₅, edi₂])
    (by rw [g₆ _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide)])
    (by rw [rd₆, u₅.rd, u₄.rd, rd₃]) (by rw [wr₆, u₅.wr, u₄.wr, wr₃]) (rs := [])
    (by rw [mm]; exact Frame.refl _ _) (by simp) (by simp), ?_, ?_, ?_, by rw [e₆, edi₅]⟩, by rw [mm, hm₂]⟩
  · rw [g₆ _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), e₃, edi₂]
  · rw [g₆ _ (by decide), u₅.other _ (by decide), u₄.gpr, m₃]; exact inv₂.arg hp (by omega)
  · rw [g₆ _ (by decide), u₅.gpr, u₄.mem, m₃]; exact inv₂.arg hp (by omega)

theorem crypt_eq : crypt =
    .seq (.block ([.mov .eax (.imm 1), .store (at_ .edi 112) .eax] ++ ptr .eax .edi 64 ++
      [.mov .ecx (.mem (at_ .esp 16)), .mov .edx (.mem (at_ .esp 20))] ++ ptr .esi .edi 128))
    (callWith [.esi, .edx, .ecx, .eax] "vg_chacha20_xor" Impl.ChaCha20.X86.Xor.xor) := rfl

theorem crB_ok {s₀ : State} (hp : APre s₀) {s : State} (h : CrA s₀ s) :
    WP isa (callWith [.esi, .edx, .ecx, .eax] "vg_chacha20_xor" Impl.ChaCha20.X86.Xor.xor) s fun s' =>
      Inv s₀ s' ∧ Frame [sub s₀ 64 384, dR s₀, stkR s₀] s.mem s'.mem ∧
      Spec.ChaCha20.bytesAt s'.mem (dp s₀) (L s₀) =
        List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt s.mem (dp s₀) (L s₀))
          (keystream (stateAt s.mem (cx s₀ + BitVec.ofNat 64 64)) (L s₀)) :=
  xor_call hp h.inv.at h.eax h.ecx h.edx h.esi fun s' at' cs' f' x' =>
    ⟨h.inv.step (cs' .edi (by simp [calleeSaved])) (by rw [at'.esp, h.inv.esp]) (by rw [at'.rd, h.inv.rd])
      (by rw [at'.wr, h.inv.wr]) f'
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact work_sub s₀ (by omega) (by omega)
        · exact ⟨dR s₀, by simp, fun _ h => h⟩
        · exact stk_work s₀)
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact sub_disj s₀ (by omega) (by omega) (by omega)
        · exact (hp.d_sub (by omega)).symm
        · exact (hp.stk_sub (by omega)).symm), f', x'⟩

theorem length_encrypt (key nonce m : List Byte) : (Spec.ChaCha20.encrypt key 1 nonce m).length = m.length := by
  rw [encrypt_eq, List.length_zipWith, VG.Proof.ChaCha20.length_keystream, Nat.min_self]

/-- The data encrypted (or decrypted) from block counter 1. -/
theorem crypt_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) :
    WP isa crypt s fun s' => Inv s₀ s' ∧ Frame [sub s₀ 64 384, dR s₀, stkR s₀] s.mem s'.mem ∧
      (stateAt s.mem (cx s₀ + BitVec.ofNat 64 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) →
        bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀))) := by
  rw [crypt_eq]
  refine WP.seq (WP.mono (crA_ok hp h) fun s₁ ⟨h₁, m₁⟩ => ?_)
  refine WP.mono (crB_ok hp h₁) fun s₂ ⟨i₂, f₂, x₂⟩ => ⟨i₂, ?_, fun hst => ?_⟩
  · refine (?_ : Frame [sub s₀ 64 384, dR s₀, stkR s₀] s.mem s₁.mem).trans f₂
    rw [m₁]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _ (contains_sub s₀ (by omega) (by omega) (by omega))
  · have d₁ : bytesAt s₁.mem (dp s₀) (L s₀) = bytesAt s.mem (dp s₀) (L s₀) := by
      rw [m₁]
      exact bytesAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self (sub s₀ 112 4)) _
        (contains_sub s₀ le_rfl (by omega) (by omega))) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hp.d_sub (by omega))
        (Nat.le_of_lt (Nat.lt_trans (LN s₀).isLt (by decide)))
    have st₁ : stateAt s₁.mem (cx s₀ + BitVec.ofNat 64 64) = Spec.ChaCha20.initState (K s₀) 1 (N s₀) := by
      rw [m₁, stateAt_ctr, hst, set12_initState]
    rw [show bytesAt = Spec.ChaCha20.bytesAt from rfl, x₂, st₁, show Spec.ChaCha20.bytesAt = bytesAt from rfl,
      d₁, encrypt_eq, VG.Proof.Poly1305.length_bytesAt]

/-! ## The tag -/

/-- Ready to call `vg_poly1305_finalize`. -/
structure FiA (s₀ : State) (out : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  ecx : s.gpr .ecx = C32 s₀ out
  eax : s.gpr .eax = 0
  edx : s.gpr .edx = C32 s₀ 656
  esi : s.gpr .esi = C32 s₀ 448

theorem fiA_ok {s₀ : State} {s : State} (h : Inv s₀ s) (out : Nat) :
    WP isa (.block (ptr .ecx .edi out ++ [.mov .eax (.imm 0)] ++ ptr .edx .edi 656 ++ ptr .esi .edi 448)) s
      fun s' => FiA s₀ out s' ∧ s'.mem = s.mem := by
  rw [show (ptr .ecx .edi out ++ [.mov .eax (.imm 0)] ++ ptr .edx .edi 656 ++ ptr .esi .edi 448 : List Instr) =
    ptr .ecx .edi out ++ (.mov .eax (.imm 0) :: (ptr .edx .edi 656 ++ ptr .esi .edi 448)) by simp]
  refine WP.block_append (WP.mono (ptr_ok .ecx .edi out s) fun s₁ ⟨e₁, g₁, rd₁, wr₁, m₁⟩ => ?_)
  refine wp_movi fun s₂ u₂ _ => ?_
  refine WP.block_append (WP.mono (ptr_ok .edx .edi 656 s₂) fun s₃ ⟨e₃, g₃, rd₃, wr₃, m₃⟩ => ?_)
  refine WP.mono (ptr_ok .esi .edi 448 s₃) fun s₄ ⟨e₄, g₄, rd₄, wr₄, m₄⟩ => ?_
  have edi₂ : s₂.gpr .edi = CX s₀ := by rw [u₂.other _ (by decide), g₁ _ (by decide), h.edi]
  have mm : s₄.mem = s.mem := by rw [m₄, m₃, u₂.mem, m₁]
  refine ⟨⟨h.step (by rw [g₄ _ (by decide), g₃ _ (by decide), edi₂, h.edi])
    (by rw [g₄ _ (by decide), g₃ _ (by decide), u₂.other _ (by decide), g₁ _ (by decide)])
    (by rw [rd₄, rd₃, u₂.rd, rd₁]) (by rw [wr₄, wr₃, u₂.wr, wr₁]) (rs := [])
    (by rw [mm]; exact Frame.refl _ _) (by simp) (by simp), ?_, ?_, ?_, ?_⟩, mm⟩
  · rw [g₄ _ (by decide), g₃ _ (by decide), u₂.other _ (by decide), e₁, h.edi]
  · rw [g₄ _ (by decide), g₃ _ (by decide), u₂.gpr]
  · rw [g₄ _ (by decide), e₃, edi₂]
  · rw [e₄, g₃ _ (by decide), edi₂]

theorem finalizeTo_eq (out : Nat) : finalizeTo out =
    .seq (.block (ptr .ecx .edi out ++ [.mov .eax (.imm 0)] ++ ptr .edx .edi 656 ++ ptr .esi .edi 448))
      (callWith [.ecx, .eax, .edx, .esi] "vg_poly1305_finalize" Impl.Poly1305.X86.finalize) := rfl

/-- What the tag's computation keeps: enough to restore the registers. -/
structure Fin (s₀ s : State) : Prop where
  at_ : At s₀ s
  edi : s.gpr .edi = CX s₀
  saved : Saved s₀ s.mem

theorem Inv.fin {s₀ s : State} (h : Inv s₀ s) : Fin s₀ s := ⟨h.at, h.edi, h.saved⟩

theorem fiB_ok {s₀ : State} (hp : APre s₀) {out : Nat} (ho : OutOk out) {s : State} (h : FiA s₀ out s) :
    WP isa (callWith [.ecx, .eax, .edx, .esi] "vg_poly1305_finalize" Impl.Poly1305.X86.finalize) s fun s' =>
      Fin s₀ s' ∧ Frame [sub s₀ 448 128, sub s₀ out 16, stkR s₀] s.mem s'.mem ∧
      ∀ key msg, Repr s.mem (cx s₀ + BitVec.ofNat 64 448) key msg →
        bytesAt s'.mem (cx s₀ + BitVec.ofNat 64 out) 16 = mac key msg := by
  refine finalize_call hp h.inv.at ho h.ecx h.eax h.edx h.esi fun s' at' cs' f' t' =>
    ⟨⟨at', by rw [cs' .edi (by simp [calleeSaved]), h.inv.edi], h.inv.saved.frame f' fun r hr => ?_⟩, f', t'⟩
  unfold OutOk at ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_disj s₀ (by omega) (by omega) (by omega)
  · exact sub_disj s₀ (by omega) (by omega) (by omega)
  · exact (hp.stk_sub (by omega)).symm

theorem finalizeTo_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) {out : Nat} (ho : OutOk out) :
    WP isa (finalizeTo out) s fun s' => Fin s₀ s' ∧ Frame [sub s₀ 448 128, sub s₀ out 16, stkR s₀] s.mem s'.mem ∧
      ∀ key msg, Repr s.mem (cx s₀ + BitVec.ofNat 64 448) key msg →
        bytesAt s'.mem (cx s₀ + BitVec.ofNat 64 out) 16 = mac key msg := by
  rw [finalizeTo_eq]
  exact WP.seq (WP.mono (fiA_ok h out) fun s₁ ⟨h₁, m₁⟩ => by rw [← m₁]; exact fiB_ok hp ho h₁)

/-! ## Restoring the registers -/

theorem restore_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Fin s₀ s) :
    WP isa (.block restore) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧
      s'.gpr .eax = s.gpr .eax ∧ s'.mem = s.mem := by
  obtain ⟨v0, v1, v2, v3⟩ := h.saved
  have i : ∀ d, d + 4 ≤ 1024 → InRegions (s.rd ++ s.wr) (cx s₀ + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [h.at_.rd, h.at_.wr]; exact hp.in_ctx' hd
  have c : ∀ d, d < 1024 → ∀ s' : State, s'.gpr .edi = CX s₀ → s'.ea (at_ .edi d) = cx s₀ + BitVec.ofNat 64 d :=
    fun d hd s' he => by rw [ea_at, he, hp.ea_ctx hd]
  refine wp_movm (c 592 (by omega) _ h.edi) (i 592 (by omega)) fun s₁ u₁ _ => ?_
  refine wp_movm (c 596 (by omega) _ (by rw [u₁.other _ (by decide), h.edi]))
    (by rw [u₁.rd, u₁.wr]; exact i 596 (by omega)) fun s₂ u₂ _ => ?_
  refine wp_movm (c 604 (by omega) _ (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.edi]))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact i 604 (by omega)) fun s₃ u₃ _ => ?_
  refine wp_movm (c 600 (by omega) _ (by rw [u₃.other _ (by decide), u₂.other _ (by decide),
    u₁.other _ (by decide), h.edi])) (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact i 600 (by omega))
    fun s₄ u₄ _ => WP.block_nil ?_
  have mm : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨fun r hr => ?_, by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
    u₁.other _ (by decide)], mm⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, v0]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, v1]
  · rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem, v2]
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, v3]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.at_.esp]

/-! ## Comparing the tags -/

theorem bytesAt4_eq {m : Mem} {p q : Addr} : bytesAt m p 4 = bytesAt m q 4 ↔ m.readW p 32 = m.readW q 32 := by
  constructor
  · intro h; apply BitVec.eq_of_toNat_eq; rw [← leNum_bytesAt_4, ← leNum_bytesAt_4, h]
  · intro h; rw [bytesAt_word, bytesAt_word, h]

theorem bytesAt16 (m : Mem) (c : Addr) (a : Nat) :
    bytesAt m (c + BitVec.ofNat 64 a) 16 = bytesAt m (c + BitVec.ofNat 64 a) 4 ++
      (bytesAt m (c + BitVec.ofNat 64 (a + 4)) 4 ++ (bytesAt m (c + BitVec.ofNat 64 (a + 8)) 4 ++
        bytesAt m (c + BitVec.ofNat 64 (a + 12)) 4)) := by
  rw [show (16 : Nat) = 4 + (4 + (4 + 4)) from rfl, VG.Proof.Poly1305.bytesAt_add,
    VG.Proof.Poly1305.bytesAt_add, VG.Proof.Poly1305.bytesAt_add]
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem app_inj {a b c d : List Byte} (h : a.length = c.length) : a ++ b = c ++ d ↔ a = c ∧ b = d :=
  ⟨fun e => List.append_inj e h, fun ⟨e₁, e₂⟩ => e₁ ▸ e₂ ▸ rfl⟩

/-- The tags differ in no bit if and only if they are equal. -/
theorem tag_eq (m : Mem) (c : Addr) :
    ((((m.readW (c + BitVec.ofNat 64 640) 32 ^^^ m.readW (c + BitVec.ofNat 64 48) 32) |||
      (m.readW (c + BitVec.ofNat 64 644) 32 ^^^ m.readW (c + BitVec.ofNat 64 52) 32)) |||
      (m.readW (c + BitVec.ofNat 64 648) 32 ^^^ m.readW (c + BitVec.ofNat 64 56) 32)) |||
      (m.readW (c + BitVec.ofNat 64 652) 32 ^^^ m.readW (c + BitVec.ofNat 64 60) 32)) = 0#32 ↔
      bytesAt m (c + BitVec.ofNat 64 640) 16 = bytesAt m (c + BitVec.ofNat 64 48) 16 := by
  have l : ∀ p, (bytesAt m p 4).length = 4 := fun p => VG.Proof.Poly1305.length_bytesAt _ _ _
  rw [bytesAt16, bytesAt16, app_inj (by rw [l, l]), app_inj (by rw [l, l]), app_inj (by rw [l, l]),
    bytesAt4_eq, bytesAt4_eq, bytesAt4_eq, bytesAt4_eq]
  simp only [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, and_assoc]

set_option simprocs false in
theorem compare_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Fin s₀ s) :
    WP isa (.block Impl.ChaCha20Poly1305.X86.compare) s fun s' =>
      s'.gpr .eax = (if bytesAt s.mem (cx s₀ + BitVec.ofNat 64 640) 16 =
        bytesAt s.mem (cx s₀ + BitVec.ofNat 64 48) 16 then 1 else 0) ∧
      (∀ q, q ≠ .eax → q ≠ .ecx → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i : ∀ d, d + 4 ≤ 1024 → InRegions (s.rd ++ s.wr) (cx s₀ + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [h.at_.rd, h.at_.wr]; exact hp.in_ctx' hd
  have e : ∀ d, d < 1024 → (CX s₀ + BitVec.ofNat 32 d).setWidth 64 = cx s₀ + BitVec.ofNat 64 d :=
    fun d hd => hp.c64 hd
  apply WP.of_runBlock
  simp (config := {decide := true}) only [Impl.ChaCha20Poly1305.X86.compare, diff, List.cons_append,
    List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.ea, at_, readSrc, execAlu, arithFlags,
    State.load32, State.setReg, State.setFlags, h.edi, e 640 (by omega), e 48 (by omega), e 644 (by omega),
    e 52 (by omega), e 648 (by omega), e 56 (by omega), e 652 (by omega), e 60 (by omega),
    i 640 (by omega), i 48 (by omega), i 644 (by omega), i 52 (by omega), i 648 (by omega), i 56 (by omega),
    i 652 (by omega), i 60 (by omega), ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun q h₁ h₂ => by simp [h₁, h₂], trivial⟩
  have ht := tag_eq s.mem (cx s₀)
  generalize ((((s.mem.readW (cx s₀ + BitVec.ofNat 64 640) 32 ^^^ s.mem.readW (cx s₀ + BitVec.ofNat 64 48) 32) |||
      (s.mem.readW (cx s₀ + BitVec.ofNat 64 644) 32 ^^^ s.mem.readW (cx s₀ + BitVec.ofNat 64 52) 32)) |||
      (s.mem.readW (cx s₀ + BitVec.ofNat 64 648) 32 ^^^ s.mem.readW (cx s₀ + BitVec.ofNat 64 56) 32)) |||
      (s.mem.readW (cx s₀ + BitVec.ofNat 64 652) 32 ^^^ s.mem.readW (cx s₀ + BitVec.ofNat 64 60) 32)) = x at ht ⊢
  by_cases hb : bytesAt s.mem (cx s₀ + BitVec.ofNat 64 640) 16 = bytesAt s.mem (cx s₀ + BitVec.ofNat 64 48) 16
  · rw [ite_eq_left hb, ht.mpr hb]; decide
  · have hx : ¬ x.toNat < 1 := fun h' => hb (ht.mp (BitVec.eq_of_toNat_eq (by simp; omega)))
    rw [ite_eq_right hb]; simp [hx]

end VG.Proof.ChaCha20Poly1305.X86
