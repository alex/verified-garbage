import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.AesGcm.X86.Tag

/-!
# AES-GCM on x86: checking a tag

Untrusted: everything here is checked by Lean. `tagLenOk` decides the tag
length (`tagLenOk_pc`), `recv` copies the received tag, padded with zeros
(`recv_ok`), `cmp o` the computed one and compares them without a branch
(`cmp_ok`), and `mask` zeroes the computed tag if they differ (`mask_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (zeros)

theorem or_eq_zero32' (a b : BitVec 32) : (a ||| b = 0) ↔ (a = 0 ∧ b = 0) := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_or] at this
    have := Nat.or_eq_zero_iff.mp this
    exact ⟨BitVec.eq_of_toNat_eq (by simpa using this.1), BitVec.eq_of_toNat_eq (by simpa using this.2)⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- What `tagLenOk` keeps of the state it starts from. -/
structure TlPost (t : Nat) (s₀ s : State) (c : Bool) : Prop where
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  other : ∀ r, r ≠ .ebx → r ≠ .ecx → s.gpr r = s₀.gpr r
  ebx : s.gpr .ebx = BitVec.ofNat 32 t
  ecx : s.gpr .ecx = BitVec.ofNat 32 (if c then 1 else 0)

theorem tagLenOk_pc {W : BitVec 32} {t : Nat} (ht : t < 2 ^ 32) :
    Pc (fun (s₀ : State) s => s = s₀ ∧ s.gpr .ebp = W ∧
        w64 (W + BitVec.ofNat 32 tglO) = w64 W + BitVec.ofNat 64 tglO ∧
        InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 tglO) 4 ∧ slotv s.mem W tglO = BitVec.ofNat 32 t)
      tagLenOk (fun s₀ s => TlPost t s₀ s (Spec.Gcm.tagLenOk t) ∧ s.zf = some (!Spec.Gcm.tagLenOk t)) := by
  -- The first comparison.
  refine Pc.seq (Q := fun s₀ s => TlPost t s₀ s false ∧ s.zf = some (decide (t = 4)))
    (Pc.taint [.ebp] (fun s₀ s ⟨hs, hb, ha, hin, hv⟩ => ?_) (fun _ _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) (by taint_decide)) ?_
  · subst hs
    rw [slotv_eq] at hv
    simp only [tglO] at hin hv ha
    refine WP.of_runBlock ⟨_, by xrun [hb, ha, hin, hv], ⟨by mems [], by mems [], by mems [], fun r h₁ h₂ => ?_, by regs [],
      by regs []; rfl⟩, ?_⟩
    · simp only [gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂, gpr_arithFlags]
    · mems []; rw [sub_beq32 ht (by decide)]
  -- `ecx := 1` if `t = 4`.
  refine Pc.seq (Q := fun s₀ s => TlPost t s₀ s (decide (t = 4))) ?_ ?_
  · refine Pc.ite (decide (t = 4)) (fun _ _ h => h.2) (fun h4 => ?_) (fun h4 => ?_)
    · exact Pc.taint [] (fun s₀ s ⟨h, _⟩ => WP.of_runBlock ⟨_, by xrun [], ⟨by mems [h.mem], by mems [h.rd],
        by mems [h.wr], fun r h₁ h₂ => by simp only [gpr_setReg_of_ne _ _ h₂]; exact h.other r h₁ h₂, by regs [h.ebx],
        by regs [h4]; rfl⟩⟩)
        (fun _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
    · exact Pc.mono Pc.nil (fun _ _ h => h) fun _ _ ⟨h, _⟩ => by rw [h4]; exact h
  -- The second.
  refine Pc.seq (Q := fun s₀ s => TlPost t s₀ s (decide (t = 4)) ∧ s.zf = some (decide (t = 8)))
    (Pc.taint [] (fun s₀ s h => WP.of_runBlock ⟨_, by xrun [h.ebx], ⟨by mems [h.mem], by mems [h.rd], by mems [h.wr],
      fun r h₁ h₂ => by regs [h.other r h₁ h₂], by regs [h.ebx], by regs [h.ecx]⟩, by
        mems []; rw [sub_beq32 ht (by decide)]⟩) (fun _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)) ?_
  refine Pc.seq (Q := fun s₀ s => TlPost t s₀ s (decide (t = 4) || decide (t = 8))) ?_ ?_
  · refine Pc.ite (decide (t = 8)) (fun _ _ h => h.2) (fun h8 => ?_) (fun h8 => ?_)
    · exact Pc.taint [] (fun s₀ s ⟨h, _⟩ => WP.of_runBlock ⟨_, by xrun [], ⟨by mems [h.mem], by mems [h.rd],
        by mems [h.wr], fun r h₁ h₂ => by simp only [gpr_setReg_of_ne _ _ h₂]; exact h.other r h₁ h₂, by regs [h.ebx],
        by regs [h8]; simp⟩⟩)
        (fun _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
    · exact Pc.mono Pc.nil (fun _ _ h => h) fun _ _ ⟨h, _⟩ => by rw [h8, Bool.or_false]; exact h
  -- `12 ≤ t ≤ 16`.
  refine Pc.seq (Q := fun s₀ s => TlPost t s₀ s (decide (t = 4) || decide (t = 8)) ∧ s.cf = some (decide (t < 12)))
    (Pc.taint [] (fun s₀ s h => WP.of_runBlock ⟨_, by xrun [h.ebx], ⟨by mems [h.mem], by mems [h.rd], by mems [h.wr],
      fun r h₁ h₂ => by regs [h.other r h₁ h₂], by regs [h.ebx], by regs [h.ecx]⟩, by
        mems []; simp [toNat_ofNat32 ht]⟩) (fun _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)) ?_
  refine Pc.seq (Q := fun s₀ s => TlPost t s₀ s (Spec.Gcm.tagLenOk t)) ?_ ?_
  · refine Pc.ite (decide (t < 12)) (fun _ _ h => h.2) (fun hl => ?_) (fun hl => ?_)
    · refine Pc.mono Pc.nil (fun _ _ h => h) fun _ _ ⟨h, _⟩ => ?_
      have hl' : t < 12 := by simpa using hl
      have : Spec.Gcm.tagLenOk t = (decide (t = 4) || decide (t = 8)) := by
        rw [Bool.eq_iff_iff]; simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
          decide_eq_true_eq]; constructor <;> intro h <;> omega
      rw [this]; exact h
    refine Pc.seq (Q := fun s₀ s => TlPost t s₀ s (decide (t = 4) || decide (t = 8)) ∧
        s.cf = some (decide (t < 17)))
      (Pc.taint [] (fun s₀ s ⟨h, _⟩ => WP.of_runBlock ⟨_, by xrun [h.ebx], ⟨by mems [h.mem], by mems [h.rd],
        by mems [h.wr], fun r h₁ h₂ => by regs [h.other r h₁ h₂], by regs [h.ebx], by regs [h.ecx]⟩, by
          mems []; simp [toNat_ofNat32 ht]⟩) (fun _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)) ?_
    refine Pc.ite (decide (t < 17)) (fun _ _ h => h.2) (fun hu => ?_) (fun hu => ?_)
    · have hl' : ¬ t < 12 := by simpa using hl
      have hu' : t < 17 := by simpa using hu
      have : Spec.Gcm.tagLenOk t = true := by
        simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]; omega
      rw [this]
      exact Pc.taint [] (fun s₀ s ⟨h, _⟩ => WP.of_runBlock ⟨_, by xrun [], ⟨by mems [h.mem], by mems [h.rd],
        by mems [h.wr], fun r h₁ h₂ => by simp only [gpr_setReg_of_ne _ _ h₂]; exact h.other r h₁ h₂, by regs [h.ebx],
        by regs []; rfl⟩⟩)
        (fun _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
    · refine Pc.mono Pc.nil (fun _ _ h => h) fun _ _ ⟨h, _⟩ => ?_
      have hl' : ¬ t < 12 := by simpa using hl
      have hu' : ¬ t < 17 := by simpa using hu
      have : Spec.Gcm.tagLenOk t = (decide (t = 4) || decide (t = 8)) := by
        rw [Bool.eq_iff_iff]; simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
          decide_eq_true_eq]; constructor <;> intro h <;> omega
      rw [this]; exact h
  -- `ZF`.
  refine Pc.taint [] (fun s₀ s h => WP.of_runBlock ⟨_, by xrun [h.ecx], ⟨by mems [h.mem], by mems [h.rd],
    by mems [h.wr], fun r h₁ h₂ => by regs [h.other r h₁ h₂], by regs [h.ebx], by regs [h.ecx]⟩, ?_⟩)
    (fun _ _ _ _ _ _ _ h => by simp at h) (by taint_decide)
  mems []
  cases Spec.Gcm.tagLenOk t <;> rfl

/-- `W` and where the tags are compared, for a run with `ebp = W`. -/
structure WEnv (W : BitVec 32) (s : State) : Prop where
  ebp : s.gpr .ebp = W
  wW : Covers [⟨w64 W, 2560⟩] s.wr
  fw : W.toNat + 2560 ≤ 2 ^ 32

theorem WEnv.keep {W : BitVec 32} {s s' : State} (h : WEnv W s) (hbp : s'.gpr .ebp = s.gpr .ebp)
    (hwr : s'.wr = s.wr) : WEnv W s' := ⟨by rw [hbp, h.ebp], by rw [hwr]; exact h.wW, h.fw⟩

theorem WEnv.aW {W : BitVec 32} {s : State} (h : WEnv W s) {o : Nat} (ho : o < 2560) :
    w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := w64_add (by have := h.fw; omega)

theorem WEnv.wIn {W : BitVec 32} {s : State} (h : WEnv W s) {o n : Nat} (ho : o + n ≤ 2560) :
    InRegions s.wr (w64 W + BitVec.ofNat 64 o) n := in_off h.wW ho (by decide)

theorem WEnv.wIn' {W : BitVec 32} {s : State} (h : WEnv W s) {o n : Nat} (ho : o + n ≤ 2560) :
    InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 o) n := in_left (h.wIn ho)

/-- The bytes at `p` after `zero4` there, then `xs` (at most 16) copied there. -/
theorem bytesAt_pad (m : Mem) (p : Addr) (xs : List Byte) (hx : xs.length ≤ 16) :
    bytesAt (writeBytes (Cmac.zero4 m p) p xs) p 16 = xs ++ zeros (16 - xs.length) := by
  rw [bytesAt_writeBytes_prefix _ _ _ hx (by decide)]
  congr 1
  have z := zero4_bytes' m p
  rw [show (16 : Nat) = xs.length + (16 - xs.length) by omega, bytesAt_add] at z
  have := congrArg (List.drop xs.length) z
  rwa [List.drop_left' (length_bytesAt _ _ _), show xs.length + (16 - xs.length) = 16 by omega, zeros,
    List.drop_replicate] at this

/-- The copy of `t` bytes from `W + o` to `W + d`, zeroed first. -/
theorem padLoop_ok {W : BitVec 32} {o d t : Nat} {m : Mem} {s : State} (he : WEnv W s)
    (hm : s.mem = Cmac.zero4 m (w64 W + BitVec.ofNat 64 d)) (hdi : s.gpr .edi = W + BitVec.ofNat 32 o)
    (hdx : s.gpr .edx = W + BitVec.ofNat 32 d) (hcx : s.gpr .ecx = BitVec.ofNat 32 t) (ht1 : 1 ≤ t)
    (ht : t ≤ 16) (ho : o + 16 ≤ d ∨ d + 16 ≤ o) (hod : o + 16 ≤ 2560) (hd : d + 16 ≤ 2560) :
    WP isa copyLoop s fun s' => bytesAt s'.mem (w64 W + BitVec.ofNat 64 d) 16 =
        bytesAt m (w64 W + BitVec.ofNat 64 o) t ++ zeros (16 - t) ∧
      Frame [⟨w64 W + BitVec.ofNat 64 d, 16⟩] m s'.mem ∧
      (∀ r, r ≠ .eax → r ≠ .edi → r ≠ .edx → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have eo := he.aW (o := o) (by omega)
  have ed := he.aW (o := d) (by omega)
  have hfw := he.fw
  have c₁ : Covers [⟨w64 W + BitVec.ofNat 64 o, t⟩] (s.rd ++ s.wr) := covers_left (covers_off he.wW (by omega) (by decide))
  have c₂ : Covers [⟨w64 W + BitVec.ofNat 64 d, t⟩] s.wr := covers_off he.wW (by omega) (by decide)
  have lp : LoopPre s (W + BitVec.ofNat 32 o) (W + BitVec.ofNat 32 d) t := by
    refine ⟨hdi, hdx, hcx, ht1, by omega, by rw [toNat_add32 (by omega)]; omega,
      by rw [toNat_add32 (by omega)]; omega, by rw [eo]; exact c₁, by rw [ed]; exact c₂, ?_⟩
    rw [eo, ed]; exact Lay.w_w (by omega) (by omega) (by omega)
  refine WP.mono (copyLoop_ok s lp) fun s' c => ?_
  have cm := c.mem
  rw [eo, ed, hm] at cm
  have fz : Frame [⟨w64 W + BitVec.ofNat 64 d, 16⟩] m (Cmac.zero4 m (w64 W + BitVec.ofNat 64 d)) :=
    Cmac.frame_store4 _ _ _ _ _
  have hS : bytesAt (Cmac.zero4 m (w64 W + BitVec.ofNat 64 d)) (w64 W + BitVec.ofNat 64 o) t =
      bytesAt m (w64 W + BitVec.ofNat 64 o) t :=
    bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (by omega) (by omega) (by omega)) (by omega)
  have hlen := length_bytesAt (Cmac.zero4 m (w64 W + BitVec.ofNat 64 d)) (w64 W + BitVec.ofNat 64 o) t
  refine ⟨?_, ?_, c.other, c.rd, c.wr⟩
  · rw [cm, bytesAt_pad _ _ _ (by rw [hlen]; exact ht), hS, length_bytesAt]
  · rw [cm]
    exact fz.trans (writeBytes_frame _ _ _ (by
      rw [hlen]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega))

theorem le4_inj {a b : BitVec 32} (h : Cmac.le4 a = Cmac.le4 b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hk : i / 8 < 4 := by omega
  have e := congrArg (fun l => l.getD (i / 8) 0) h
  simp only [Cmac.getD_le4 _ hk] at e
  have := congrArg (fun x => x.getLsbD (i % 8)) e
  simp only [BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega, decide_true, Bool.true_and] at this
  rwa [show 8 * (i / 8) + i % 8 = i by omega] at this

theorem xor_eq_zero32 (a b : BitVec 32) : (a ^^^ b = 0) ↔ a = b := by
  constructor
  · intro h
    have := congrArg (· ^^^ b) h
    simpa [BitVec.xor_assoc] using this
  · intro h; subst h; simp

/-- Four words equal, if and only if their XORs `or`ed are zero. -/
theorem xor4_eq_zero (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : BitVec 32) :
    ((a₀ ^^^ b₀) ||| (a₁ ^^^ b₁) ||| (a₂ ^^^ b₂) ||| (a₃ ^^^ b₃) = 0) ↔ (a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃) := by
  simp only [or_eq_zero32', xor_eq_zero32, and_assoc]

/-- Sixteen bytes equal, if and only if their four words are. -/
theorem bytes16_eq (m : Mem) (p q : Addr) :
    bytesAt m p 16 = bytesAt m q 16 ↔ (m.readW p 32 = m.readW q 32 ∧
      m.readW (p + BitVec.ofNat 64 4) 32 = m.readW (q + BitVec.ofNat 64 4) 32 ∧
      m.readW (p + BitVec.ofNat 64 8) 32 = m.readW (q + BitVec.ofNat 64 8) 32 ∧
      m.readW (p + BitVec.ofNat 64 12) 32 = m.readW (q + BitVec.ofNat 64 12) 32) := by
  rw [bytesAt16, bytesAt16, ← Cmac.le4_readW, ← Cmac.le4_readW, ← Cmac.le4_readW, ← Cmac.le4_readW,
    ← Cmac.le4_readW, ← Cmac.le4_readW, ← Cmac.le4_readW, ← Cmac.le4_readW]
  constructor
  · intro h
    simp only [List.append_assoc] at h
    obtain ⟨h₀, h⟩ := List.append_inj h (by simp [Cmac.length_le4])
    obtain ⟨h₁, h⟩ := List.append_inj h (by simp [Cmac.length_le4])
    obtain ⟨h₂, h₃⟩ := List.append_inj h (by simp [Cmac.length_le4])
    exact ⟨le4_inj h₀, le4_inj h₁, le4_inj h₂, le4_inj h₃⟩
  · rintro ⟨h₀, h₁, h₂, h₃⟩; rw [h₀, h₁, h₂, h₃]

theorem cmpTail_ok {W : BitVec 32} {s : State} (he : WEnv W s) :
    WP isa (.block cmpTail) s fun s' => s'.gpr .eax = BitVec.ofNat 32
        (if bytesAt s.mem (w64 W + BitVec.ofNat 64 vO) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 rO) 16
          then 1 else 0) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) := by
  have aW : ∀ {o}, o < 2560 → w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := fun ho => he.aW ho
  have rIn : ∀ {o}, o + 4 ≤ 2560 → InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 o) 4 := fun ho => he.wIn' ho
  refine WP.of_runBlock ⟨_, by xrun [cmpTail, he.ebp, aW, rIn], ?_, ?_, ?_, ?_, ?_⟩
  · regs []
    simp only [bytes16_eq, add_ofNat_assoc, Nat.reduceAdd]
    generalize s.mem.readW (w64 W + BitVec.ofNat 64 240) 32 = a₀
    generalize s.mem.readW (w64 W + BitVec.ofNat 64 244) 32 = a₁
    generalize s.mem.readW (w64 W + BitVec.ofNat 64 248) 32 = a₂
    generalize s.mem.readW (w64 W + BitVec.ofNat 64 252) 32 = a₃
    generalize s.mem.readW (w64 W + BitVec.ofNat 64 256) 32 = b₀
    generalize s.mem.readW (w64 W + BitVec.ofNat 64 260) 32 = b₁
    generalize s.mem.readW (w64 W + BitVec.ofNat 64 264) 32 = b₂
    generalize s.mem.readW (w64 W + BitVec.ofNat 64 268) 32 = b₃
    have e := xor4_eq_zero a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
    by_cases h : a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      simp only [and_self, ↓reduceIte, BitVec.xor_self, BitVec.or_self]
      decide
    · have h0 : (a₀ ^^^ b₀) ||| (a₁ ^^^ b₁) ||| (a₂ ^^^ b₂) ||| (a₃ ^^^ b₃) ≠ 0 := fun h' => h (e.mp h')
      have hne : ((a₀ ^^^ b₀) ||| (a₁ ^^^ b₁) ||| (a₂ ^^^ b₂) ||| (a₃ ^^^ b₃)).toNat ≠ 0 := fun h' =>
        h0 (BitVec.eq_of_toNat_eq (by simpa using h'))
      have hlt : ¬ ((a₀ ^^^ b₀) ||| (a₁ ^^^ b₁) ||| (a₂ ^^^ b₂) ||| (a₃ ^^^ b₃)).toNat < (BitVec.ofNat 32 1).toNat := by
        rw [BitVec.toNat_ofNat]; omega
      simp only [h, ↓reduceIte, decide_eq_false hlt]
      rfl
  · mems []
  · mems []
  · mems []
  · intro r h₁ h₂
    simp only [gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂, gpr_arithFlags, gpr_setFlags]

/-- `zero4 d` folded. -/
theorem zero4_fold (m : Mem) (W : BitVec 32) (d : Nat) :
    (((m.writeW (w64 W + BitVec.ofNat 64 d) (BitVec.ofNat 32 0)).writeW (w64 W + BitVec.ofNat 64 (d + 4))
      (BitVec.ofNat 32 0)).writeW (w64 W + BitVec.ofNat 64 (d + 8)) (BitVec.ofNat 32 0)).writeW
      (w64 W + BitVec.ofNat 64 (d + 12)) (BitVec.ofNat 32 0) = Cmac.zero4 m (w64 W + BitVec.ofNat 64 d) := by
  simp only [Cmac.zero4, Cmac.store4, add_ofNat_assoc]; rfl

theorem recv_ok {W : BitVec 32} {t : Nat} {s : State} (he : WEnv W s) (hv : slotv s.mem W tglO = BitVec.ofNat 32 t)
    (ht1 : 1 ≤ t) (ht : t ≤ 16) :
    WP isa recv s fun s' => bytesAt s'.mem (w64 W + BitVec.ofNat 64 rO) 16 = bytesAt s.mem (w64 W) t ++ zeros (16 - t) ∧
      Frame [⟨w64 W + BitVec.ofNat 64 rO, 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esi = s.gpr .esi ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have aW : ∀ {o}, o < 2560 → w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := fun ho => he.aW ho
  have wIn : ∀ {o}, o + 4 ≤ 2560 → InRegions s.wr (w64 W + BitVec.ofNat 64 o) 4 := fun ho => he.wIn ho
  have rIn : ∀ {o}, o + 4 ≤ 2560 → InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 o) 4 := fun ho => he.wIn' ho
  rw [slotv_eq] at hv
  simp only [tglO] at hv
  have hz := zero4_fold s.mem W 256
  simp only [Nat.reduceAdd] at hz
  have hv' : (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 256)).readW (w64 W + BitVec.ofNat 64 180) 32 =
      BitVec.ofNat 32 t := by
    have fz : Frame [⟨w64 W + BitVec.ofNat 64 256, 16⟩] s.mem (Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 256)) :=
      Cmac.frame_store4 _ _ _ _ _
    rw [slot_frame (W := W) (o := 180) fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (W := W) (a := 180) (n := 4) (d := 256) (k := 16) (by decide) (by decide) (by decide))]
    exact hv
  refine WP.seq (WP.of_runBlock ⟨_, by xrun [recv, zero4, he.ebp, aW, wIn, rIn, readW_writeW_off, hv, hz, hv'], ?_⟩)
  refine WP.mono (padLoop_ok (o := 0) (d := 256) (t := t) (m := s.mem) (he.keep (by regs []) (by mems []))
    (by mems []) (by regs [he.ebp]; exact (BitVec.add_zero W).symm) (by regs [he.ebp]) (by regs []) ht1 ht
    (.inl (by decide)) (by decide) (by decide)) fun s' ⟨b, f, g, rd, wr⟩ => ⟨?_, f, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using b
  · rw [g _ (by decide) (by decide) (by decide) (by decide)]; regs []
  · rw [g _ (by decide) (by decide) (by decide) (by decide)]; regs []
  · rw [g _ (by decide) (by decide) (by decide) (by decide)]; regs []
  · rw [rd]; mems []
  · rw [wr]; mems []

theorem recv_ct {I : State → Prop} {W : BitVec 32} {t : Nat}
    (h : ∀ s, I s → WEnv W s ∧ slotv s.mem W tglO = BitVec.ofNat 32 t) : CT I recv := by
  refine CT.seq (J := fun s => s.gpr .edi = W ∧ s.gpr .edx = W + BitVec.ofNat 32 rO ∧ s.gpr .ecx = BitVec.ofNat 32 t)
    (CT.taint [.ebp] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(h _ h₁).1.ebp, (h _ h₂).1.ebp]) (by taint_decide))
    (fun s hs => ?_) (copyLoop_ct fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2, h₂.2.2])
  obtain ⟨he, hv⟩ := h s hs
  have aW : ∀ {o}, o < 2560 → w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := fun ho => he.aW ho
  have wIn : ∀ {o}, o + 4 ≤ 2560 → InRegions s.wr (w64 W + BitVec.ofNat 64 o) 4 := fun ho => he.wIn ho
  have rIn : ∀ {o}, o + 4 ≤ 2560 → InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 o) 4 := fun ho => he.wIn' ho
  rw [slotv_eq] at hv
  simp only [tglO] at hv
  exact WP.of_runBlock ⟨_, by xrun [zero4, he.ebp, aW, wIn, rIn, readW_writeW_off, hv], by regs [he.ebp],
    by regs [he.ebp], by regs []⟩

end VG.Proof.AesGcm.X86
