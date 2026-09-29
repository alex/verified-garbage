import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Stages

/-!
# ChaCha20-Poly1305 on ARMv7: correctness

Untrusted: everything here is checked by Lean. `seal` and `open`, from their
parts: up to the arguments of `vg_poly1305_finalize` (`sealMain`,
`openMain`), the frame around it (`finalize`), and the rest (`sealEnd`,
`openEnd`). The constant-time proof runs the taint analysis on the first and
the last, and relates the two runs of the frame by what these theorems say
of the states between them.
-/

namespace VG.Proof.ChaCha20Poly1305.Arm

open VG VG.Arm VG.Impl.ChaCha20Poly1305.Arm
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

/-- The ciphertext `seal` computes. -/
abbrev Ct (s₀ : State) : List Byte := Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀)

theorem srcA {s₀ : State} (hp : APre s₀) : Src s₀ (aP s₀) (AL s₀) :=
  ⟨(s₀.gpr .r2).isLt, hp.fit_a, hp.c_a, fun a n ⟨r, hr, hc⟩ => ⟨r, by
    simp only [List.mem_singleton] at hr; subst hr; simp [hp.rd], hc⟩⟩

theorem srcD {s₀ : State} (hp : APre s₀) : Src s₀ (dP s₀) (L s₀) :=
  ⟨(stackArg s₀ 0).isLt, hp.fit_d, hp.c_d, fun a n ⟨r, hr, hc⟩ => ⟨r, by
    simp only [List.mem_singleton] at hr; subst hr; simp [hp.wr], hc⟩⟩

theorem hAL (s₀ : State) : s₀.gpr .r2 = BitVec.ofNat 32 (AL s₀) := by simp [AL]

/-- The additional data is unchanged. -/
theorem aad_eq {s₀ s : State} (hp : APre s₀) (h : Inv s₀ s) : bytesAt s.mem (ad s₀) (AL s₀) = A s₀ :=
  bytesAt_frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.c_a.symm
    · exact hp.a_d
    · exact hp.b_a.symm) (by have := (s₀.gpr .r2).isLt; simp only [AL]; omega)

/-- The data is unchanged by a frame of the context and the stack below. -/
theorem data_frame {s₀ : State} (hp : APre s₀) {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, ∃ k n, k + n ≤ 1024 ∧ Region.Sub r (sub s₀ k n) ∨ r = belR s₀) :
    bytesAt m' (dp s₀) (L s₀) = bytesAt m (dp s₀) (L s₀) :=
  bytesAt_frame hf (fun r hr => by
    obtain ⟨k, n, h⟩ := hd r hr
    rcases h with ⟨hk, hs⟩ | rfl
    · exact (hp.c_d.sub_left (sub_ctx s₀ hk)).symm.sub_right hs
    · exact hp.b_d.symm) (by have := (stackArg s₀ 0).isLt; simp only [L]; omega)

theorem sub_self' (s₀ : State) (k n : Nat) : Region.Sub (sub s₀ k n) (sub s₀ k n) := fun _ h => h

theorem macData_eq (a c : List Byte) :
    macData a c = [] ++ (a ++ pad16 a) ++ (c ++ pad16 c) ++ (leBytes 8 a.length ++ leBytes 8 c.length) := by
  simp [macData, List.append_assoc]

/-! ## Up to the frame -/

/-- The MAC so far, from the Poly1305 state for the one-time key: the
additional data and the text `x`, padded, and the lengths. -/
theorem mac_parts {s₀ s₁ s₂ s₃ s₄ : State} {x : List Byte} (hx : x.length = L s₀)
    (hr₁ : Repr s₁.mem (cx s₀) (otk s₀) [])
    (ha : ∀ key msg, Repr s₁.mem (cx s₀) key msg → Repr s₂.mem (cx s₀) key (msg ++
      (bytesAt s₁.mem (ad s₀) (AL s₀) ++ pad16 (bytesAt s₁.mem (ad s₀) (AL s₀)))))
    (hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀)
    (hd : ∀ key msg, Repr s₂.mem (cx s₀) key msg → Repr s₃.mem (cx s₀) key (msg ++ (x ++ pad16 x)))
    (hl : ∀ key msg, Repr s₃.mem (cx s₀) key msg →
      Repr s₄.mem (cx s₀) key (msg ++ (leBytes 8 (AL s₀) ++ leBytes 8 (L s₀)))) :
    Repr s₄.mem (cx s₀) (otk s₀) (macData (A s₀) x) := by
  have := hl _ _ (hd _ _ (ha _ _ hr₁))
  rw [hA] at this
  rwa [macData_eq, show (A s₀).length = AL s₀ from VG.Proof.Poly1305.length_bytesAt _ _ _, hx]

theorem count_eq {s₀ : State} {x : List Byte} (hx : x.length = L s₀) :
    BitVec.ofNat 64 (16 * ((AL s₀ + 15) / 16 + (L s₀ + 15) / 16 + 1)) =
      BitVec.ofNat 64 (macData (A s₀) x).length := by
  rw [length_macData, hx, show (A s₀).length = AL s₀ from VG.Proof.Poly1305.length_bytesAt _ _ _]

/-- Before the frame in `seal`. -/
structure PreFs (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  r0 : s.gpr .r0 = cP s₀
  r1 : s.gpr .r1 = ptr s₀ tagOff
  r12 : s.gpr .r12 = ptr s₀ scrOff
  cnt : Proof.Poly1305.countArm s = BitVec.ofNat 64 (macData (A s₀) (Ct s₀)).length
  repr : Repr s.mem (cx s₀) (otk s₀) (macData (A s₀) (Ct s₀))
  data : bytesAt s.mem (dp s₀) (L s₀) = Ct s₀

theorem sealMain_ok {s₀ : State} (hp : APre s₀) : WP isa sealMain s₀ (PreFs s₀) := by
  unfold sealMain
  refine WP.seq (WP.mono (block1_seal_ok hp) fun s₁ h₁ => ?_)
  have d₁ : bytesAt s₁.mem (dp s₀) (L s₀) = D s₀ :=
    data_frame hp h₁.fctx fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨0, 1024, .inl ⟨le_rfl, by rw [sub_zero]; exact fun _ h => h⟩⟩
  refine WP.seq (WP.mono (keyGen_ok hp h₁) fun s₂ ⟨h₂, f₂⟩ => ?_)
  have d₂ : bytesAt s₂.mem (dp s₀) (L s₀) = D s₀ := by
    rw [data_frame hp f₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨0, 256, .inl ⟨by omega, sub_self' _ _ _⟩⟩
      · exact ⟨keyOff, 32, .inl ⟨by simp [keyOff], sub_self' _ _ _⟩⟩, d₁]
  refine WP.seq (WP.mono (crypt_ok hp h₂.inv h₂.st) fun s₃ ⟨i₃, k₃, c₃⟩ => ?_)
  rw [d₂] at c₃
  have key₃ : bytesAt s₃.mem (off (cx s₀) keyOff) 32 = otk s₀ := by
    rw [bytesAt_frame k₃.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact sub_disj s₀ (by simp [keyOff, stOff]) (by simp [keyOff]) (by simp [stOff])
        · exact hp.c_d.sub_left (sub_ctx s₀ (by simp [keyOff]))) (by omega), h₂.key]
  refine WP.seq (WP.mono (polyInit_ok hp i₃ key₃) fun s₄ ⟨i₄, k₄, r₄⟩ => ?_)
  have c₄ : bytesAt s₄.mem (dp s₀) (L s₀) = Ct s₀ := by
    rw [data_frame hp k₄.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨0, 128, .inl ⟨by omega, sub_self' _ _ _⟩⟩, c₃]
  refine WP.seq (WP.mono (macPad_ok hp (p := .r8) (n := .r9) ⟨.inl rfl, .inl rfl⟩ (srcA hp) i₄ i₄.regs.r8
    (by rw [i₄.regs.r9]; exact hAL s₀)) fun s₅ ⟨i₅, k₅, r₅⟩ => ?_)
  have hmac : ∀ r ∈ macR s₀, ∃ k n, k + n ≤ 1024 ∧ Region.Sub r (sub s₀ k n) ∨ r = belR s₀ := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨0, 128, .inl ⟨by omega, sub_self' _ _ _⟩⟩
    · exact ⟨padOff, 16, .inl ⟨by simp [padOff], sub_self' _ _ _⟩⟩
  have c₅ : bytesAt s₅.mem (dp s₀) (L s₀) = Ct s₀ := by rw [data_frame hp k₅.frame hmac, c₄]
  refine WP.seq (WP.mono (macPad_ok hp (p := .r10) (n := .r11) ⟨.inr rfl, .inr rfl⟩ (srcD hp) i₅ i₅.regs.r10
    (by rw [i₅.regs.r11]; exact hL s₀)) fun s₆ ⟨i₆, k₆, r₆⟩ => ?_)
  have c₆ : bytesAt s₆.mem (dp s₀) (L s₀) = Ct s₀ := by rw [data_frame hp k₆.frame hmac, c₅]
  refine WP.seq (WP.mono (lengths_ok hp i₆) fun s₇ ⟨i₇, k₇, r₇⟩ => ?_)
  have c₇ : bytesAt s₇.mem (dp s₀) (L s₀) = Ct s₀ := by
    rw [data_frame hp k₇.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨0, 128, .inl ⟨by omega, sub_self' _ _ _⟩⟩
      · exact ⟨lenOff, 16, .inl ⟨by simp [lenOff], sub_self' _ _ _⟩⟩, c₆]
  refine WP.mono (finArgs_ok i₇) fun s₈ ⟨i₈, k₈, h0, h1, h12, hc⟩ => ?_
  have hlen : (Ct s₀).length = L s₀ := by
    rw [length_encrypt, VG.Proof.Poly1305.length_bytesAt]
  refine ⟨i₈, h0, h1, h12, by rw [hc, count_eq hlen], ?_, by rw [k₈.mem_eq, c₇]⟩
  rw [k₈.mem_eq]
  refine mac_parts hlen r₄ r₅ (aad_eq hp i₄) ?_ r₇
  rw [c₅] at r₆
  exact r₆

/-! ## The frame -/

/-- After the frame in `seal`. -/
structure PostFs (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  tag : bytesAt s.mem (off (cx s₀) tagOff) 16 = mac (otk s₀) (macData (A s₀) (Ct s₀))
  data : bytesAt s.mem (dp s₀) (L s₀) = Ct s₀

theorem finalize_seal_ok {s₀ : State} (hp : APre s₀) {s : State} (h : PreFs s₀ s) :
    WP isa finalize s (PostFs s₀) :=
  WP.mono (fin_ok hp h.inv h.r0 h.r1 h.r12) fun s' ⟨i', k', t'⟩ =>
    ⟨i', t' _ _ h.repr h.cnt, by
      rw [data_frame hp k'.frame fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨0, 128, .inl ⟨by omega, sub_self' _ _ _⟩⟩
        · exact ⟨tagOff, 16, .inl ⟨by simp [tagOff], sub_self' _ _ _⟩⟩
        · exact ⟨scrOff, 128, .inl ⟨by simp [scrOff], sub_self' _ _ _⟩⟩
        · exact ⟨0, 0, .inr rfl⟩, h.data]⟩

/-! ## After the frame -/

/-- The callee-saved registers restored, and the stack pointer as on entry. -/
theorem abi_of {s₀ s' : State} (hr : ∀ r ∈ preserved, s'.gpr r = s₀.gpr r) (hsp : s'.sp = s₀.sp) :
    abiPreserved s₀ s' := ⟨hr, hsp⟩

theorem sealEnd_ok {s₀ : State} (hp : APre s₀) {s : State} (h : PostFs s₀ s) :
    WP isa (.block sealEnd) s fun s' => abiPreserved s₀ s' ∧ sealArm.post s₀ s' := by
  unfold sealEnd
  refine WP.block_append (WP.mono (copyWords_ok hp (a := tagOff) (b := 48) (n := 4) (by simp [tagOff])
    (by simp [tagOff]) (by omega) h.inv.regs.r7 (Inv.ctxOk hp h.inv.rd h.inv.wr))
    fun s₁ ⟨g₁, rd₁, wr₁, sp₁, f₁, w₁⟩ => ?_)
  have hk₁ : Kept [sub s₀ 48 (4 * 4)] s s₁ :=
    ⟨fun r hr _ => g₁ r (by rintro rfl; simp [preserved] at hr), sp₁, rd₁, wr₁, f₁⟩
  have i₁ := h.inv.step1 hk₁ (by omega) (by simp [savOff])
  refine WP.mono (restore_ok hp i₁.regs.r7 i₁.saved i₁.rd i₁.wr) fun s₂ ⟨g₂, _, m₂, sp₂, _, _⟩ =>
    ⟨abi_of g₂ (by rw [sp₂, i₁.sp]), ?_⟩
  show Spec.ChaCha20Poly1305.encrypt (K s₀) (N s₀) (A s₀) (D s₀) =
    (bytesAt s₂.mem (dp s₀) (L s₀), bytesAt s₂.mem (cx s₀ + 48) 16)
  have t₁ : bytesAt s₁.mem (off (cx s₀) 48) (4 * 4) = bytesAt s.mem (off (cx s₀) tagOff) (4 * 4) :=
    bytes_of_words fun k hk => by rw [off_add, off_add]; exact w₁ k hk
  rw [m₂, show cx s₀ + 48 = off (cx s₀) 48 from rfl, show (16 : Nat) = 4 * 4 from rfl, t₁,
    data_frame hp f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨48, 16, .inl ⟨by omega, sub_self' _ _ _⟩⟩,
    h.data]
  simp only [Spec.ChaCha20Poly1305.encrypt]
  rw [show (4 * 4 : Nat) = 16 from rfl, h.tag]

theorem seal_correct {s₀ : State} (hp : APre s₀) :
    WP isa Impl.ChaCha20Poly1305.Arm.«seal» s₀ fun s' => abiPreserved s₀ s' ∧ sealArm.post s₀ s' :=
  WP.seq (WP.mono (sealMain_ok hp) fun _ h => WP.seq (WP.mono (finalize_seal_ok hp h)
    fun _ h' => sealEnd_ok hp h'))

/-! ## Open -/

/-- A part of the context is unchanged by a frame of other parts of it, the
data and the stack below. -/
theorem ctx_disj {s₀ : State} (hp : APre s₀) {rs : List Region} {a n : Nat} (ha : a + n ≤ 1024)
    (hd : ∀ r ∈ rs, (∃ k l, k + l ≤ 1024 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = sub s₀ k l) ∨ r = dR s₀ ∨ r = belR s₀) :
    ∀ r ∈ rs, (sub s₀ a n).Disjoint r := by
  intro r hr
  rcases hd r hr with ⟨k, l, hk, hkl, rfl⟩ | rfl | rfl
  · exact sub_disj s₀ (by omega) ha hk
  · exact hp.c_d.sub_left (sub_ctx s₀ ha)
  · exact (hp.b_c.sub_right (sub_ctx s₀ ha)).symm

theorem ctx_bytes {s₀ : State} (hp : APre s₀) {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {a n : Nat}
    (ha : a + n ≤ 1024)
    (hd : ∀ r ∈ rs, (∃ k l, k + l ≤ 1024 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = sub s₀ k l) ∨ r = dR s₀ ∨ r = belR s₀) :
    bytesAt m' (off (cx s₀) a) n = bytesAt m (off (cx s₀) a) n :=
  bytesAt_frame hf (ctx_disj hp ha hd) (by omega)

theorem ctx_state {s₀ : State} (hp : APre s₀) {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (∃ k l, k + l ≤ 1024 ∧ (k + l ≤ stOff ∨ stOff + 64 ≤ k) ∧ r = sub s₀ k l) ∨ r = dR s₀ ∨
      r = belR s₀) :
    stateAt m' (off (cx s₀) stOff) = stateAt m (off (cx s₀) stOff) :=
  stateAt_frame hf (ctx_disj hp (a := stOff) (n := 64) (by simp [stOff]) hd)

/-- Before the frame in `open`. -/
structure PreFo (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  r0 : s.gpr .r0 = cP s₀
  r1 : s.gpr .r1 = ptr s₀ tagOff
  r12 : s.gpr .r12 = ptr s₀ scrOff
  cnt : Proof.Poly1305.countArm s = BitVec.ofNat 64 (macData (A s₀) (D s₀)).length
  repr : Repr s.mem (cx s₀) (otk s₀) (macData (A s₀) (D s₀))
  data : bytesAt s.mem (dp s₀) (L s₀) = D s₀
  st : stateAt s.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)
  rt : bytesAt s.mem (off (cx s₀) rtagOff) 16 = T0 s₀

/-- The regions `macPad` writes, as `ctx_bytes` wants them. -/
theorem macR_hd (s₀ : State) {a n : Nat} (h : 128 ≤ a) (h' : padOff + 16 ≤ a ∨ a + n ≤ padOff) :
    ∀ r ∈ macR s₀, (∃ k l, k + l ≤ 1024 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = sub s₀ k l) ∨ r = dR s₀ ∨
      r = belR s₀ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inl ⟨0, 128, by omega, by omega, rfl⟩
  · exact .inl ⟨padOff, 16, by simp [padOff], h', rfl⟩

theorem openMain_ok {s₀ : State} (hp : APre s₀) : WP isa openMain s₀ (PreFo s₀) := by
  unfold openMain
  refine WP.seq (WP.mono (block1_open_ok hp) fun s₁ h₁ => ?_)
  have d₁ : bytesAt s₁.mem (dp s₀) (L s₀) = D s₀ :=
    data_frame hp h₁.fctx fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨0, 1024, .inl ⟨le_rfl, by rw [sub_zero]; exact fun _ h => h⟩⟩
  refine WP.seq (WP.mono (keyGen_ok hp h₁.toPost1) fun s₂ ⟨h₂, f₂⟩ => ?_)
  have hd₂ : ∀ r ∈ [sub s₀ 0 256, sub s₀ keyOff 32], ∃ k n, k + n ≤ 1024 ∧ Region.Sub r (sub s₀ k n) ∨
      r = belR s₀ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨0, 256, .inl ⟨by omega, sub_self' _ _ _⟩⟩
    · exact ⟨keyOff, 32, .inl ⟨by simp [keyOff], sub_self' _ _ _⟩⟩
  have d₂ : bytesAt s₂.mem (dp s₀) (L s₀) = D s₀ := by rw [data_frame hp f₂ hd₂, d₁]
  have rt₂ : bytesAt s₂.mem (off (cx s₀) rtagOff) 16 = T0 s₀ := by
    rw [ctx_bytes hp f₂ (by simp [rtagOff]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl ⟨0, 256, by omega, by simp [rtagOff], rfl⟩
      · exact .inl ⟨keyOff, 32, by simp [keyOff], by simp [keyOff, rtagOff], rfl⟩, h₁.rt]
  refine WP.seq (WP.mono (polyInit_ok hp h₂.inv h₂.key) fun s₃ ⟨i₃, k₃, r₃⟩ => ?_)
  have hd₀ : ∀ {a n : Nat}, 128 ≤ a → ∀ r ∈ [sub s₀ 0 128],
      (∃ k l, k + l ≤ 1024 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = sub s₀ k l) ∨ r = dR s₀ ∨ r = belR s₀ :=
    fun ha r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inl ⟨0, 128, by omega, by omega, rfl⟩
  have d₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by
    rw [data_frame hp k₃.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨0, 128, .inl ⟨by omega, sub_self' _ _ _⟩⟩, d₂]
  have st₃ : stateAt s₃.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [ctx_state hp k₃.frame (hd₀ (by simp [stOff])), h₂.st]
  have rt₃ : bytesAt s₃.mem (off (cx s₀) rtagOff) 16 = T0 s₀ := by
    rw [ctx_bytes hp k₃.frame (by simp [rtagOff]) (hd₀ (by simp [rtagOff])), rt₂]
  refine WP.seq (WP.mono (macPad_ok hp (p := .r8) (n := .r9) ⟨.inl rfl, .inl rfl⟩ (srcA hp) i₃ i₃.regs.r8
    (by rw [i₃.regs.r9]; exact hAL s₀)) fun s₄ ⟨i₄, k₄, r₄⟩ => ?_)
  have hmac : ∀ r ∈ macR s₀, ∃ k n, k + n ≤ 1024 ∧ Region.Sub r (sub s₀ k n) ∨ r = belR s₀ := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨0, 128, .inl ⟨by omega, sub_self' _ _ _⟩⟩
    · exact ⟨padOff, 16, .inl ⟨by simp [padOff], sub_self' _ _ _⟩⟩
  have d₄ : bytesAt s₄.mem (dp s₀) (L s₀) = D s₀ := by rw [data_frame hp k₄.frame hmac, d₃]
  have st₄ : stateAt s₄.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [ctx_state hp k₄.frame (macR_hd s₀ (by simp [stOff]) (by simp [stOff, padOff])), st₃]
  have rt₄ : bytesAt s₄.mem (off (cx s₀) rtagOff) 16 = T0 s₀ := by
    rw [ctx_bytes hp k₄.frame (by simp [rtagOff]) (macR_hd s₀ (by simp [rtagOff]) (by simp [rtagOff, padOff])),
      rt₃]
  refine WP.seq (WP.mono (macPad_ok hp (p := .r10) (n := .r11) ⟨.inr rfl, .inr rfl⟩ (srcD hp) i₄ i₄.regs.r10
    (by rw [i₄.regs.r11]; exact hL s₀)) fun s₅ ⟨i₅, k₅, r₅⟩ => ?_)
  have d₅ : bytesAt s₅.mem (dp s₀) (L s₀) = D s₀ := by rw [data_frame hp k₅.frame hmac, d₄]
  have st₅ : stateAt s₅.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [ctx_state hp k₅.frame (macR_hd s₀ (by simp [stOff]) (by simp [stOff, padOff])), st₄]
  have rt₅ : bytesAt s₅.mem (off (cx s₀) rtagOff) 16 = T0 s₀ := by
    rw [ctx_bytes hp k₅.frame (by simp [rtagOff]) (macR_hd s₀ (by simp [rtagOff]) (by simp [rtagOff, padOff])),
      rt₄]
  refine WP.seq (WP.mono (lengths_ok hp i₅) fun s₆ ⟨i₆, k₆, r₆⟩ => ?_)
  have hl : ∀ {a n : Nat}, 128 ≤ a → (lenOff + 16 ≤ a ∨ a + n ≤ lenOff) → ∀ r ∈ [sub s₀ 0 128, sub s₀ lenOff 16],
      (∃ k l, k + l ≤ 1024 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = sub s₀ k l) ∨ r = dR s₀ ∨ r = belR s₀ :=
    fun ha ha' r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl ⟨0, 128, by omega, by omega, rfl⟩
      · exact .inl ⟨lenOff, 16, by simp [lenOff], ha', rfl⟩
  have d₆ : bytesAt s₆.mem (dp s₀) (L s₀) = D s₀ := by
    rw [data_frame hp k₆.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨0, 128, .inl ⟨by omega, sub_self' _ _ _⟩⟩
      · exact ⟨lenOff, 16, .inl ⟨by simp [lenOff], sub_self' _ _ _⟩⟩, d₅]
  have st₆ : stateAt s₆.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [ctx_state hp k₆.frame (hl (by simp [stOff]) (by simp [stOff, lenOff])), st₅]
  have rt₆ : bytesAt s₆.mem (off (cx s₀) rtagOff) 16 = T0 s₀ := by
    rw [ctx_bytes hp k₆.frame (by simp [rtagOff]) (hl (by simp [rtagOff]) (by simp [rtagOff, lenOff])), rt₅]
  refine WP.mono (finArgs_ok i₆) fun s₇ ⟨i₇, k₇, h0, h1, h12, hc⟩ => ?_
  have hlen : (D s₀).length = L s₀ := VG.Proof.Poly1305.length_bytesAt _ _ _
  have m₇ := k₇.mem_eq
  refine ⟨i₇, h0, h1, h12, by rw [hc, count_eq hlen], ?_, by rw [m₇, d₆], by rw [m₇, st₆], by rw [m₇, rt₆]⟩
  rw [m₇]
  refine mac_parts hlen r₃ r₄ (aad_eq hp i₃) ?_ r₆
  rw [d₄] at r₅
  exact r₅

/-- After the frame in `open`. -/
structure PostFo (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  tag : bytesAt s.mem (off (cx s₀) tagOff) 16 = mac (otk s₀) (macData (A s₀) (D s₀))
  data : bytesAt s.mem (dp s₀) (L s₀) = D s₀
  st : stateAt s.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)
  rt : bytesAt s.mem (off (cx s₀) rtagOff) 16 = T0 s₀

theorem fin_hd (s₀ : State) {a n : Nat} (h : 128 ≤ a) (h' : tagOff + 16 ≤ a ∨ a + n ≤ tagOff)
    (h'' : scrOff + 128 ≤ a ∨ a + n ≤ scrOff) :
    ∀ r ∈ [sub s₀ 0 128, sub s₀ tagOff 16, sub s₀ scrOff 128, belR s₀],
      (∃ k l, k + l ≤ 1024 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = sub s₀ k l) ∨ r = dR s₀ ∨ r = belR s₀ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inl ⟨0, 128, by omega, by omega, rfl⟩
  · exact .inl ⟨tagOff, 16, by simp [tagOff], h', rfl⟩
  · exact .inl ⟨scrOff, 128, by simp [scrOff], h'', rfl⟩
  · exact .inr (.inr rfl)

theorem finalize_open_ok {s₀ : State} (hp : APre s₀) {s : State} (h : PreFo s₀ s) :
    WP isa finalize s (PostFo s₀) :=
  WP.mono (fin_ok hp h.inv h.r0 h.r1 h.r12) fun s' ⟨i', k', t'⟩ =>
    ⟨i', t' _ _ h.repr h.cnt, by
      rw [data_frame hp k'.frame fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨0, 128, .inl ⟨by omega, sub_self' _ _ _⟩⟩
        · exact ⟨tagOff, 16, .inl ⟨by simp [tagOff], sub_self' _ _ _⟩⟩
        · exact ⟨scrOff, 128, .inl ⟨by simp [scrOff], sub_self' _ _ _⟩⟩
        · exact ⟨0, 0, .inr rfl⟩, h.data],
      by rw [ctx_state hp k'.frame (fin_hd s₀ (by simp [stOff]) (by simp [stOff, tagOff])
        (by simp [stOff, scrOff])), h.st],
      by rw [ctx_bytes hp k'.frame (by simp [rtagOff]) (fin_hd s₀ (by simp [rtagOff]) (by simp [rtagOff, tagOff])
        (by simp [rtagOff, scrOff])), h.rt]⟩

theorem openEnd_ok {s₀ : State} (hp : APre s₀) {s : State} (h : PostFo s₀ s) :
    WP isa openEnd s fun s' => abiPreserved s₀ s' ∧ openArm.post s₀ s' := by
  unfold openEnd
  refine WP.seq (WP.mono (crypt_ok hp h.inv h.st) fun s₁ ⟨i₁, k₁, c₁⟩ => ?_)
  have hc : ∀ {a n : Nat}, stOff + 64 ≤ a → a + n ≤ 1024 → ∀ r ∈ [sub s₀ 0 (stOff + 64), dR s₀],
      (∃ k l, k + l ≤ 1024 ∧ (k + l ≤ a ∨ a + n ≤ k) ∧ r = sub s₀ k l) ∨ r = dR s₀ ∨ r = belR s₀ :=
    fun ha _ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl ⟨0, stOff + 64, by simp [stOff], by omega, rfl⟩
      · exact .inr (.inl rfl)
  have t₁ : bytesAt s₁.mem (off (cx s₀) tagOff) 16 = mac (otk s₀) (macData (A s₀) (D s₀)) := by
    rw [ctx_bytes hp k₁.frame (by simp [tagOff]) (hc (by simp [stOff, tagOff]) (by simp [tagOff])), h.tag]
  have rt₁ : bytesAt s₁.mem (off (cx s₀) rtagOff) 16 = T0 s₀ := by
    rw [ctx_bytes hp k₁.frame (by simp [rtagOff]) (hc (by simp [stOff, rtagOff]) (by simp [rtagOff])), h.rt]
  rw [h.data] at c₁
  refine WP.block_append (WP.mono (compare_ok hp i₁.regs.r7 i₁.rd i₁.wr)
    fun s₂ ⟨r0₂, g₂, sp₂, m₂, rd₂, wr₂⟩ => ?_)
  have i₂ : Inv s₀ s₂ := i₁.step0 ⟨fun r hr _ => g₂ r hr, sp₂, rd₂, wr₂, by rw [m₂]; exact Frame.refl _ _⟩
  refine WP.mono (restore_ok hp i₂.regs.r7 i₂.saved i₂.rd i₂.wr) fun s₃ ⟨g₃, o₃, m₃, sp₃, _, _⟩ =>
    ⟨abi_of g₃ (by rw [sp₃, i₂.sp]), ?_⟩
  have r0₃ : s₃.gpr .r0 = if mac (otk s₀) (macData (A s₀) (D s₀)) = T0 s₀ then 1 else 0 := by
    rw [o₃ .r0 (by decide) (by decide), r0₂, t₁, rt₁]
  have d₃ : bytesAt s₃.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [m₃, m₂, c₁]
  show (match Spec.ChaCha20Poly1305.decrypt (K s₀) (N s₀) (A s₀) (D s₀) (T0 s₀) with
    | some pt => s₃.gpr .r0 = 1 ∧ bytesAt s₃.mem (dp s₀) (L s₀) = pt
    | none => s₃.gpr .r0 = 0)
  simp only [Spec.ChaCha20Poly1305.decrypt]
  by_cases e : mac (otk s₀) (macData (A s₀) (D s₀)) = T0 s₀
  · simp only [otk] at e
    simp only [e, ↓reduceIte]
    exact ⟨by rw [r0₃]; simp [e], d₃⟩
  · simp only [otk] at e
    simp only [e, ↓reduceIte]
    rw [r0₃]; simp [e]

theorem open_correct {s₀ : State} (hp : APre s₀) :
    WP isa Impl.ChaCha20Poly1305.Arm.«open» s₀ fun s' => abiPreserved s₀ s' ∧ openArm.post s₀ s' :=
  WP.seq (WP.mono (openMain_ok hp) fun _ h => WP.seq (WP.mono (finalize_open_ok hp h)
    fun _ h' => openEnd_ok hp h'))

end VG.Proof.ChaCha20Poly1305.Arm
