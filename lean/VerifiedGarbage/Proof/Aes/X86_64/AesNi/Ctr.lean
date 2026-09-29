import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds

/-!
# AES-NI counter mode: the counter blocks and the data

Untrusted: everything here is checked by Lean. `ctrs_ok`: `ctrs regs` puts
the counter blocks `CB`, `inc₃₂(CB)`, … into the registers `regs`, as bytes;
`xorData_ok`: `xorData regs j` XORs the registers into the data blocks
`j`, `j + 1`, …; both for any list of registers, by induction.
-/

namespace VG.Proof.Aes.X86_64.AesNi

open VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_ ctrs xorData)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_xor)
open VG.Spec.Gcm (Block blockAt inc32)

/-- `xmm11`: 1 in doubleword 0. -/
abbrev one : BitVec 128 := (0 : BitVec 64) ++ (1 : BitVec 64)

theorem paddd_one (c : Block) : XBinOp.eval .paddd c one = inc32 c := by
  have z : ∀ x : BitVec 32, x + 0 = x := fun x => BitVec.add_zero x
  have e0 : dword one 0 = 1 := by decide
  have e1 : dword one 1 = 0 := by decide
  have e2 : dword one 2 = 0 := by decide
  have e3 : dword one 3 = 0 := by decide
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [XBinOp.eval, e0, e1, e2, e3, z, getLsbD_ofDwords, getLsbD_dword, inc32,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases (by omega : i < 32 ∨ (32 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96) ∨ 96 ≤ i) with h | h | h | h <;>
  simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and] <;>
  first
  | rfl
  | exact congrArg _ (by omega)

theorem rep_succ' {α : Type} (f : α → α) (a : α) : ∀ k, Nat.repeat f k (f a) = Nat.repeat f (k + 1) a
  | 0 => rfl
  | k + 1 => congrArg f (rep_succ' f a k)

theorem rep_add {α : Type} (f : α → α) (a : α) (i : Nat) :
    ∀ k, Nat.repeat f k (Nat.repeat f i a) = Nat.repeat f (i + k) a
  | 0 => rfl
  | k + 1 => congrArg f (rep_add f a i k)

/-- One counter block into `b`. -/
theorem ctr1_ok (b : XReg) (s : State) (h9 : b ≠ .xmm9) (h10 : b ≠ .xmm10) (h11 : b ≠ .xmm11)
    (hr : s.xmm .xmm10 = revMask) (ho : s.xmm .xmm11 = one) :
    WP isa (.block [.xop (.bin .movdqa b .xmm9), .xop (.bin .pshufb b .xmm10),
        .xop (.bin .paddd .xmm9 .xmm11)]) s fun s' =>
      s'.xmm b = XBinOp.eval .pshufb (s.xmm .xmm9) revMask ∧ s'.xmm .xmm9 = inc32 (s.xmm .xmm9) ∧
      XFrame [b, .xmm9] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, ite_true, ite_false, eval_movdqa, h9, Ne.symm h9, Ne.symm h10,
    Ne.symm h11, hr, ho, paddd_one,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2, ite_false]

theorem ctrs_ok (regs : List XReg) (s : State) (hnd : regs.Nodup)
    (hx : ∀ r ∈ regs, r ≠ .xmm9 ∧ r ≠ .xmm10 ∧ r ≠ .xmm11)
    (hr : s.xmm .xmm10 = revMask) (ho : s.xmm .xmm11 = one) :
    WP isa (.block (ctrs regs)) s fun s' =>
      (∀ k (h : k < regs.length),
        s'.xmm regs[k] = XBinOp.eval .pshufb (Nat.repeat inc32 k (s.xmm .xmm9)) revMask) ∧
      s'.xmm .xmm9 = Nat.repeat inc32 regs.length (s.xmm .xmm9) ∧ XFrame (.xmm9 :: regs) s s' := by
  induction regs generalizing s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), rfl, XFrame.refl _ _⟩
  | cons b bs ih =>
    obtain ⟨h9, h10, h11⟩ := hx b List.mem_cons_self
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    rw [ctrs, WP.block_append_iff]
    refine WP.mono (ctr1_ok b s h9 h10 h11 hr ho) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_
    refine WP.mono (ih s₁ (List.nodup_cons.mp hnd).2 (fun r h => hx r (List.mem_cons_of_mem _ h))
      (by rw [f₁.xmm _ (by simp [Ne.symm h10])]; exact hr)
      (by rw [f₁.xmm _ (by simp [Ne.symm h11])]; exact ho)) fun s' ⟨e, c, f⟩ => ⟨?_, ?_, ?_⟩
    · intro k hk
      cases k with
      | zero =>
        simp only [List.getElem_cons_zero]
        rw [f.xmm _ (by simp [h9, hbs]), e₁]; rfl
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [e k (by simpa using hk), c₁, rep_succ']
    · rw [c, c₁, rep_succ', List.length_cons]
    · refine (f₁.comp f).mono fun r hr => ?_
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h) | h | h <;> simp [h]

/-! ## The data -/

theorem eval_pxor (a b : BitVec 128) : XBinOp.eval .pxor a b = a ^^^ b := rfl

theorem blockAt_writeW_sep (m : Mem) {p q : Addr} (v : BitVec 128) (h : Mem.Sep q 16 p 16) :
    blockAt (m.writeW p v) q = blockAt m q := by
  rw [blockAt_eq, blockAt_eq, Mem.readW_writeW_sep h (by decide)]

/-- The block at `p` after XORing `x` (as bytes) into it. -/
theorem blockAt_writeW_xor (m : Mem) (p : Addr) (x : BitVec 128) :
    blockAt (m.writeW p (XBinOp.eval .pxor x (m.readW p 128))) p =
      blockAt m p ^^^ XBinOp.eval .pshufb x revMask := by
  rw [blockAt_eq, blockAt_eq, Mem.readW_writeW_self m p 16 _ (by decide), eval_pxor,
    pshufb_rev_xor, BitVec.xor_comm]

/-- A block of a region disjoint from the frame's is unchanged. -/
theorem blockAt_frame {rs : List Region} {m m' : Mem} (h : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 16⟩ r) : blockAt m' p = blockAt m p :=
  Proof.Gcm.blockAt_congr fun _ hk => h.bytes (R := ⟨p, 16⟩) hd (by show (16 : Nat) ≤ 2 ^ 64; decide) hk

theorem inRegions_wr {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) :
    InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- XOR `b` into the block at `rcx + d`. -/
theorem xor1_ok (b : XReg) (d : Nat) (s : State) (hb8 : b ≠ .xmm8)
    (hin : InRegions s.wr (s.gpr .rcx + BitVec.ofInt 64 (d : Int)) 16) :
    WP isa (.block [.movdquLoad .xmm8 (at_ .rcx d), .xop (.bin .pxor b .xmm8),
        .movdquStore (at_ .rcx d) b]) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rcx + BitVec.ofInt 64 (d : Int))
        (XBinOp.eval .pxor (s.xmm b) (s.mem.readW (s.gpr .rcx + BitVec.ofInt 64 (d : Int)) 128)) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ .xmm8 → s'.xmm r = s.xmm r) := by
  have hin' := inRegions_wr hin
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, State.load128, State.store128, ea_at, hin, hin', ite_true, ite_false, hb8,
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, fun r h1 h2 => by simp [h1, h2]⟩

theorem xorData_ok (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs)
    (hin : ∀ k < regs.length,
      InRegions s.wr (s.gpr .rcx + BitVec.ofInt 64 ((16 * (j + k) : Nat) : Int)) 16)
    (hw : (s.gpr .rcx).toNat + 16 * (j + regs.length) ≤ 2 ^ 64) :
    WP isa (.block (xorData regs j)) s fun s' =>
      (∀ k (h : k < regs.length), blockAt s'.mem (s.gpr .rcx + BitVec.ofNat 64 (16 * (j + k))) =
        blockAt s.mem (s.gpr .rcx + BitVec.ofNat 64 (16 * (j + k))) ^^^
          XBinOp.eval .pshufb (s.xmm regs[k]) revMask) ∧
      Frame [⟨s.gpr .rcx + BitVec.ofNat 64 (16 * j), 16 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .xmm8 → r ∉ regs → s'.xmm r = s.xmm r) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl,
      fun _ _ _ => rfl⟩
  | cons b bs ih =>
    have hb8 : b ≠ .xmm8 := fun h => h8 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h8' : .xmm8 ∉ bs := fun h => h8 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hin hw
    rw [xorData, WP.block_append_iff]
    have hin0 := hin 0 (by omega)
    rw [Nat.add_zero] at hin0
    refine WP.mono (xor1_ok b (16 * j) s hb8 hin0) fun s₁ ⟨m₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have hrcx : s₁.gpr .rcx = s.gpr .rcx := by rw [g₁]
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2 h8' (fun k hk => by
        rw [wr₁, hrcx, show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega))
      (by rw [hrcx]; omega)) fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    rw [hrcx] at hb hf
    have ofs : ∀ a : Nat, (s.gpr .rcx + BitVec.ofInt 64 (a : Int)) = s.gpr .rcx + BitVec.ofNat 64 a :=
      fun a => by rw [ofInt_natCast]
    rw [ofs] at m₁
    -- Block `j` is not in the rest's frame.
    have hdj : ∀ r ∈ [(⟨s.gpr .rcx + BitVec.ofNat 64 (16 * (j + 1)), 16 * bs.length⟩ : Region)],
        Region.Disjoint ⟨s.gpr .rcx + BitVec.ofNat 64 (16 * j), 16⟩ r := by
      simp only [List.mem_singleton, forall_eq]
      intro a h₁ h₂
      simp only [Region.Contains] at h₁ h₂
      rw [off_toNat _ _ (by omega)] at h₁ h₂
      have := (a - s.gpr .rcx).isLt
      omega
    refine ⟨fun k hk => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r hr hr' => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [blockAt_frame hf hdj, m₁, blockAt_writeW_xor]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        rw [show j + (k + 1) = j + 1 + k by omega, hb k hk', m₁, blockAt_writeW_sep _ _ (by
            intro a h₁ h₂
            rw [off_toNat _ _ (by omega)] at h₁ h₂
            have := (a - s.gpr .rcx).isLt
            omega),
          x₁ _ (fun h => hbs (h ▸ List.getElem_mem hk')) (fun h => h8' (h ▸ List.getElem_mem hk'))]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨s.gpr .rcx + BitVec.ofNat 64 (16 * j), 16 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega)).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at ha ⊢
      rw [off_toNat _ _ (by omega)] at ha ⊢
      have := (a - s.gpr .rcx).isLt
      omega
    · simp only [List.mem_cons, not_or] at hr'
      rw [hx r hr hr'.2, x₁ r hr'.1 hr]

end VG.Proof.Aes.X86_64.AesNi
