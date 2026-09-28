import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.MacPad
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Prologue

/-!
# ChaCha20-Poly1305 on x86-64: the other parts

Untrusted: everything here is checked by Lean. The lengths block, the
encryption, absorbing the lengths, the tag, comparing tags, and restoring the
registers.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt keystream)

theorem sub_sub (s₀ : State) {a m k n : Nat} (h₁ : a ≤ k) (h₂ : k + n ≤ a + m) (h₃ : a + m ≤ 1024) :
    Region.Sub (sub s₀ k n) (sub s₀ a m) := by
  intro x hx
  simp only [off_eq, Region.Contains] at *
  have e : x - (cx s₀ + BitVec.ofNat 64 a) = (x - (cx s₀ + BitVec.ofNat 64 k)) + BitVec.ofNat 64 (k - a) := by
    rw [show k = a + (k - a) by omega, BitVec.ofNat_add]; bv_omega
  rw [e, BitVec.toNat_add, toNat_ofNat_lt (by omega)]
  exact le_trans (Nat.add_le_add_right (Nat.mod_le _ _) _) (by omega)

theorem calleeSaved_rsp : Reg.rsp ∈ calleeSaved := by simp [calleeSaved]

/-- The invariant survives a part that keeps the callee-saved registers and
writes only the working space, the data and the stack. -/
theorem Inv.step {s₀ s s' : State} (h : Inv s₀ s) (cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [workR s₀, dR s₀, stkR s₀], Region.Sub r r')
    (hsv : ∀ r ∈ rs, (sub s₀ 592 40).Disjoint r) : Inv s₀ s' where
  r15 := by rw [cs _ (by simp [calleeSaved]), h.r15]
  r14 := by rw [cs _ (by simp [calleeSaved]), h.r14]
  r13 := by rw [cs _ (by simp [calleeSaved]), h.r13]
  r12 := by rw [cs _ (by simp [calleeSaved]), h.r12]
  rsp := by rw [cs _ calleeSaved_rsp, h.rsp]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  saved := h.saved.frame hf hsv
  frame := h.frame.trans (hf.sub hsub)

/-- `ctx[k, k + n)` in the working space. -/
theorem sub_work (s₀ : State) {k n : Nat} (h₁ : 64 ≤ k) (h₂ : k + n ≤ 1024) :
    ∃ r' ∈ [workR s₀, dR s₀, stkR s₀], Region.Sub (sub s₀ k n) r' :=
  ⟨workR s₀, by simp, sub_sub s₀ h₁ (by omega) (by omega)⟩

theorem stk_work (s₀ : State) : ∃ r' ∈ [workR s₀, dR s₀, stkR s₀], Region.Sub (stkR s₀) r' :=
  ⟨stkR s₀, by simp, fun _ h => h⟩

theorem mac_inv {s₀ s s' : State} (hp : APre s₀) (h : Inv s₀ s) (cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame (macR s₀) s.mem s'.mem) : Inv s₀ s' :=
  h.step cs hrd hwr hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_work s₀ (by omega) (by omega)
      · exact stk_work s₀)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj s₀ (by omega) (by omega) (by omega)
      · exact (hp.stk_sub (by omega)).symm)

/-! ## The lengths block -/

theorem bytesAt_16 (m : Mem) (p : Addr) :
    bytesAt m p 16 = leBytes 8 (m.readW p 64).toNat ++ leBytes 8 (m.readW (off p 8) 64).toNat := by
  rw [show 16 = 8 + 8 from rfl, VG.Proof.Poly1305.bytesAt_add, VG.Proof.Poly1305.bytesAt_leBytes_64,
    VG.Proof.Poly1305.bytesAt_leBytes_64, off_eq]

set_option simprocs false in
theorem lengths_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) (hrbp : s.gpr .rbp = s₀.gpr .rdx) :
    WP isa (.block lengths) s fun s' => Inv s₀ s' ∧ (∀ r, s'.gpr r = s.gpr r) ∧
      Frame [sub s₀ 656 16] s.mem s'.mem ∧
      bytesAt s'.mem (off (cx s₀) 656) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
  have o0 := hp.in_ctx (a := 656) (w := 8) (by omega)
  have o1 := hp.in_ctx (a := 664) (w := 8) (by omega)
  rw [← h.wr] at o0 o1
  simp only [off] at o0 o1
  apply WP.of_runBlock
  simp (config := {decide := true}) only [lengths, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    State.store64, h.r15, o0, o1, ite_true, Option.some.injEq, exists_eq_left']
  have hf : Frame [sub s₀ 656 16] s.mem ((s.mem.writeW (off (cx s₀) 656) (s.gpr .rbp)).writeW
      (off (cx s₀) 664) (s.gpr .r13)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub s₀ le_rfl (by omega) (by omega))
      |>.writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by omega) (by omega) (by omega))
  refine ⟨h.step (fun _ _ => rfl) rfl rfl hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_work s₀ (by omega) (by omega))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_disj s₀ (by omega) (by omega) (by omega)),
    fun _ => trivial, hf, ?_⟩
  rw [bytesAt_16, off_off, show 656 + 8 = 664 from rfl, readW64_off _ _ _ (by omega) (by omega) (by omega),
    Mem.readW_writeW_self64, Mem.readW_writeW_self64, hrbp, h.r13]

/-! ## Restoring the registers -/

set_option simprocs false in
theorem restore_ok {s₀ : State} (hp : APre s₀) {s : State} (hrdi : s.gpr .rdi = off (cx s₀) 448)
    (hsv : Saved s₀ s.mem) (hr12 : s.gpr .r12 = s₀.gpr .r12) (hrsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block restore) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧
      s'.gpr .rax = s.gpr .rax ∧ s'.mem = s.mem := by
  have i : ∀ d, 448 ≤ d → d + 8 ≤ 1024 → InRegions (s.rd ++ s.wr) (off (off (cx s₀) 448) (d - 448)) 8 := by
    intro d h₁ h₂
    rw [off_off, show 448 + (d - 448) = d by omega, hrd, hwr]; exact hp.in_ctx' h₂
  have i0 := i 592 (by omega) (by omega)
  have i1 := i 600 (by omega) (by omega)
  have i2 := i 608 (by omega) (by omega)
  have i3 := i 616 (by omega) (by omega)
  have i4 := i 624 (by omega) (by omega)
  obtain ⟨v0, v1, v2, v3, v4⟩ := hsv
  have e : ∀ d, 448 ≤ d → off (off (cx s₀) 448) (d - 448) = off (cx s₀) d := fun d h => by
    rw [off_off, show 448 + (d - 448) = d by omega]
  rw [← e 592 (by omega)] at v0
  rw [← e 600 (by omega)] at v1
  rw [← e 608 (by omega)] at v2
  rw [← e 616 (by omega)] at v3
  rw [← e 624 (by omega)] at v4
  apply WP.of_runBlock
  simp (config := {decide := true}) only [restore, saved, List.map_cons, List.map_nil, runBlock_cons,
    runStep_some, runBlock_nil, exec, ea_at, readSrc, State.load64, State.setReg, hrdi, i0, i1, i2, i3, i4,
    v0, v1, v2, v3, v4, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [ite_true, ite_false, hr12, hrsp]

/-! ## Comparing the tags -/

theorem bytesAt_8_eq {m : Mem} {p q : Addr} :
    bytesAt m p 8 = bytesAt m q 8 ↔ m.readW p 64 = m.readW q 64 := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [← VG.Proof.Poly1305.leNum_bytesAt_64, ← VG.Proof.Poly1305.leNum_bytesAt_64, h]
  · intro h
    rw [VG.Proof.Poly1305.bytesAt_leBytes_64, VG.Proof.Poly1305.bytesAt_leBytes_64, h]

/-- The tags differ in no bit if and only if they are equal. -/
theorem tag_eq (m : Mem) (p q : Addr) :
    ((m.readW p 64 ^^^ m.readW q 64) ||| (m.readW (off p 8) 64 ^^^ m.readW (off q 8) 64)) = 0#64 ↔
      bytesAt m p 16 = bytesAt m q 16 := by
  rw [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, BitVec.xor_eq_zero_iff, show 16 = 8 + 8 from rfl,
    VG.Proof.Poly1305.bytesAt_add, VG.Proof.Poly1305.bytesAt_add, ← off_eq, ← off_eq, ← bytesAt_8_eq,
    ← bytesAt_8_eq]
  constructor
  · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]
  · intro h
    exact List.append_inj h (by rw [VG.Proof.Poly1305.length_bytesAt, VG.Proof.Poly1305.length_bytesAt])

theorem ea_disp (s : State) (b : Reg) (d : Int) :
    s.ea { base := b, disp := d } = s.gpr b + BitVec.ofInt 64 d := rfl

theorem off_neg {p : Addr} {a d : Nat} (h : d ≤ a) :
    off p a + BitVec.ofInt 64 (-(d : Int)) = off p (a - d) := by
  rw [off_eq, off_eq]
  have : BitVec.ofInt 64 (-(d : Int)) = 0 - BitVec.ofNat 64 d := by
    rw [BitVec.ofInt_neg, BitVec.ofInt_natCast]; simp
  rw [this, show a = (a - d) + d by omega, BitVec.ofNat_add, Nat.add_sub_cancel]
  bv_omega

set_option simprocs false in
theorem compare_ok {s₀ : State} (hp : APre s₀) {s : State} (hrcx : s.gpr .rcx = off (cx s₀) 640)
    (hrdi : s.gpr .rdi = off (cx s₀) 448) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block compare) s fun s' =>
      (s'.gpr .rax).setWidth 32 =
        (if bytesAt s.mem (off (cx s₀) 640) 16 = bytesAt s.mem (off (cx s₀) 48) 16 then 1 else 0) ∧
      (∀ q, q ≠ .rax → q ≠ .rdx → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e0 : off (off (cx s₀) 640) 0 = off (cx s₀) 640 := by rw [off_off]
  have e1 : off (cx s₀) 448 + BitVec.ofInt 64 (-400) = off (cx s₀) 48 := off_neg (d := 400) (by omega)
  have e3 : off (cx s₀) 448 + BitVec.ofInt 64 (-392) = off (off (cx s₀) 48) 8 := by
    rw [off_off]; exact off_neg (d := 392) (by omega)
  have i : ∀ a, a + 8 ≤ 1024 → InRegions (s.rd ++ s.wr) (off (cx s₀) a) 8 := fun a h => by
    rw [hrd, hwr]; exact hp.in_ctx' h
  have i0 := i 640 (by omega)
  have i1 := i 48 (by omega)
  have i2 : InRegions (s.rd ++ s.wr) (off (off (cx s₀) 640) 8) 8 := by rw [off_off]; exact i 648 (by omega)
  have i3 : InRegions (s.rd ++ s.wr) (off (off (cx s₀) 48) 8) 8 := by rw [off_off]; exact i 56 (by omega)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [VG.Impl.ChaCha20Poly1305.X86_64.compare, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    ea_disp, readSrc, readSrc32, execAlu, execAlu32, arithFlags, State.load64, State.setReg, State.setReg32,
    State.setFlags, hrcx, hrdi, e0, e1, e3, i0, i1, i2, i3, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', se1']
  refine ⟨?_, fun q h₁ h₂ => by simp [h₁, h₂], trivial⟩
  have ht := tag_eq s.mem (off (cx s₀) 640) (off (cx s₀) 48)
  generalize ((s.mem.readW (off (cx s₀) 640) 64 ^^^ s.mem.readW (off (cx s₀) 48) 64) |||
    (s.mem.readW (off (off (cx s₀) 640) 8) 64 ^^^ s.mem.readW (off (off (cx s₀) 48) 8) 64)) = x at ht ⊢
  by_cases hb : bytesAt s.mem (off (cx s₀) 640) 16 = bytesAt s.mem (off (cx s₀) 48) 16
  · rw [ite_eq_left hb, ht.mpr hb]; decide
  · have hx : ¬ x.toNat < 1 := fun h => hb (ht.mp (BitVec.eq_of_toNat_eq (by simp; omega)))
    rw [ite_eq_right hb]; simp [hx]

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
    stateAt (m.writeW (off c 112) (1 : BitVec 32)) (off c 64) = (stateAt m (off c 64)).set 12 1 := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_set, Vector.getElem_ofFn]
  rw [show off c 64 + BitVec.ofNat 64 (4 * i) = off c (64 + 4 * i) by
    simp only [off_eq, BitVec.ofNat_add, BitVec.add_assoc]]
  by_cases h : 12 = i
  · subst h; simp only [ite_true]; exact Mem.readW_writeW_self32 _ _ _
  · simp only [h, ite_false]
    exact readW32_off m c 1 (by omega) (by omega) (by omega)

set_option simprocs false in
theorem cryptA_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block ([.mov32 .rax (.imm 1), .store32 (at_ .r15 112) .rax] ++ ptr .rdi .r15 64 ++
      [.mov .rsi (.reg .r14), .mov .rdx (.reg .r13)] ++ ptr .rcx .r15 128)) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32) ∧ s'.gpr .rdi = off (cx s₀) 64 ∧
      s'.gpr .rsi = dp s₀ ∧ s'.gpr .rdx = s₀.gpr .r8 ∧ s'.gpr .rcx = off (cx s₀) 128 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o := hp.in_ctx (a := 112) (w := 4) (by omega)
  rw [← h.wr] at o
  simp only [off] at o
  apply WP.of_runBlock
  simp (config := {decide := true}) only [ptr, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec, ea_at, readSrc, readSrc32, execAlu, arithFlags, State.store32, State.setReg,
    State.setReg32, State.setFlags, h.r15, h.r14, h.r13, o, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', se_ofNat (show 64 < 2 ^ 31 by omega),
    se_ofNat (show 128 < 2 ^ 31 by omega), BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  refine ⟨trivial, by rw [off_eq], trivial, trivial, by rw [off_eq], fun r hr => ?_, trivial⟩
  have := calleeSaved_ne hr
  simp [this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2]

theorem hL (s₀ : State) : s₀.gpr .r8 = BitVec.ofNat 64 (L s₀) := by simp [L]

/-- The data encrypted (or decrypted) from block counter 1. -/
theorem crypt_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)) :
    WP isa crypt s fun s' => Inv s₀ s' ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      Frame [sub s₀ 64 384, dR s₀, stkR s₀] s.mem s'.mem ∧
      bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  refine WP.seq (WP.mono (cryptA_ok hp h) fun s₁ ⟨m₁, rdi₁, rsi₁, rdx₁, rcx₁, cs₁, rd₁, wr₁⟩ => ?_)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [cs₁ _ calleeSaved_rsp, h.rsp]
  have wr₁' : s₁.wr = s₀.wr := by rw [wr₁, h.wr]
  have hw : Covers [⟨off (cx s₀) 64, 64⟩, ⟨dp s₀, L s₀⟩, ⟨off (cx s₀) 128, 320⟩] s₁.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by simp [wr₁', hp.wr], 64, by simp [off_eq], by show 64 + 64 ≤ 1024; omega⟩
    · exact ⟨dR s₀, by simp [wr₁', hp.wr], 0, by simp, by simp⟩
    · exact ⟨ctxR s₀, by simp [wr₁', hp.wr], 128, by simp [off_eq], by show 128 + 320 ≤ 1024; omega⟩
  refine WP.seq (xor_call rdi₁ rsi₁ (by rw [rdx₁]; exact hL s₀) rcx₁ (s₀.gpr .r8).isLt
    (hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by omega)))
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by omega) (by omega) (by omega))
    (hp.c_d.symm.sub_right (sub_ctx s₀ (k := 128) (n := 320) (by omega))) hp.wrap_d
    (by rw [rsp₁]; exact hp.stk_sub (by omega)) (by rw [rsp₁]; exact hp.stk_d)
    (by rw [rsp₁]; exact hp.stk_sub (by omega)) (covers_nil_append (covers_left _ hw)) hw
    fun s₂ rd₂ wr₂ cs₂ f₂ rsi₂ data₂ => ?_)
  rw [rsp₁] at f₂
  refine WP.mono (anchor_ok .rsi (k := 128) (by omega) s₂) fun s₃ ⟨e3, g₃, rd₃, wr₃, m₃⟩ => ?_
  have cs : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r := fun r hr => by
    by_cases h15 : r = .r15
    · subst h15; rw [e3, rsi₂, off_sub, h.r15]
    · rw [g₃ r h15, cs₂ r hr, cs₁ r hr]
  have f1 : Frame [sub s₀ 64 64] s.mem s₁.mem := by
    rw [m₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by omega) (by omega) (by omega))
  have hsub : ∀ r ∈ [sub s₀ 64 384, dR s₀, stkR s₀], ∃ r' ∈ [workR s₀, dR s₀, stkR s₀], Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_work s₀ (by omega) (by omega)
    · exact ⟨dR s₀, by simp, fun _ h => h⟩
    · exact stk_work s₀
  have hf : Frame [sub s₀ 64 384, dR s₀, stkR s₀] s.mem s₃.mem := by
    rw [m₃]
    refine (f1.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ le_rfl (by omega) (by omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ le_rfl (by omega) (by omega)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by omega) (by omega) (by omega)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  refine ⟨h.step cs (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁]) hf hsub (fun r hr => ?_), cs, hf, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_disj s₀ (by omega) (by omega) (by omega)
    · exact hp.c_d.sub_left (sub_ctx s₀ (by omega))
    · exact (hp.stk_sub (by omega)).symm
  · have d₁ : bytesAt s₁.mem (dp s₀) (L s₀) = bytesAt s.mem (dp s₀) (L s₀) :=
      bytesAt_frame f1 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.c_d.sub_left (sub_ctx s₀ (by omega))).symm) (s₀.gpr .r8).isLt.le
    have st₁ : stateAt s₁.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 1 (N s₀) := by
      rw [m₁, stateAt_ctr, hst, set12_initState]
    rw [m₃, ← bytesAt_eq, data₂, st₁, bytesAt_eq, d₁, encrypt_eq, VG.Proof.Poly1305.length_bytesAt]

/-! ## Absorbing the lengths and the tag -/

set_option simprocs false in
theorem ptrs_ok (k : Nat) (hk : k < 2 ^ 31) (v : BitVec 32) (s : State) :
    WP isa (.block (ptr .rdi .r15 448 ++ ptr .rsi .r15 k ++ [.mov32 .rdx (.imm v)])) s fun s' =>
      s'.gpr .rdi = off (s.gpr .r15) 448 ∧ s'.gpr .rsi = off (s.gpr .r15) k ∧ s'.gpr .rdx = v.setWidth 64 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [ptr, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, readSrc32, execAlu, arithFlags, State.setReg, State.setReg32, State.setFlags,
    ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    se_ofNat (show 448 < 2 ^ 31 by omega), se_ofNat hk]
  refine ⟨by rw [off_eq], by rw [off_eq], trivial, fun r hr => ?_, trivial⟩
  have := calleeSaved_ne hr
  simp [this.2.2.1, this.2.2.2.1, this.2.2.2.2]

theorem absorbLengths_eq : absorbLengths =
    .seq (.block (ptr .rdi .r15 448 ++ ptr .rsi .r15 656 ++ [.mov32 .rdx (.imm 1)]))
    (.seq (.call "vg_poly1305_blocks" Impl.Poly1305.X86_64.blocks) (.block (anchor .rdi 448))) := rfl

/-- The lengths block absorbed. -/
theorem absorbLengths_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) :
    WP isa absorbLengths s fun s' => Inv s₀ s' ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      Frame (macR s₀) s.mem s'.mem ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        Repr s'.mem (off (cx s₀) 448) key (msg ++ bytesAt s.mem (off (cx s₀) 656) 16) := by
  rw [absorbLengths_eq]
  refine WP.seq (WP.mono (ptrs_ok 656 (by omega) 1 s) fun s₁ ⟨rdi₁, rsi₁, rdx₁, cs₁, rd₁, wr₁, m₁⟩ => ?_)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [cs₁ _ calleeSaved_rsp, h.rsp]
  have wr₁' : s₁.wr = s₀.wr := by rw [wr₁, h.wr]
  rw [h.r15] at rdi₁ rsi₁
  refine WP.seq (blocks_call (n := 1) rdi₁ rsi₁ (by rw [rdx₁]; rfl) (by omega)
    (sub_disj s₀ (b := 656) (m := 16 * 1) (by omega) (by omega) (by omega))
    (by rw [hp.off_toNat (by omega)]; have := hp.wrap_c; omega)
    (by rw [rsp₁]; exact hp.below8_sub (by omega)) (by rw [rsp₁]; exact hp.below8_sub (by omega))
    (covers_left _ (covers_sub hp wr₁' _ (by
      intro r hr; simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨656, rfl, show 656 + 16 * 1 ≤ 1024 by omega⟩
      · exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩)))
    (covers_sub hp wr₁' _ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩))
    fun s₂ rd₂ wr₂ cs₂ f₂ rdi₂ repr₂ => ?_)
  rw [rsp₁, m₁] at f₂
  rw [m₁] at repr₂
  refine WP.mono (anchor_ok .rdi (k := 448) (by omega) s₂) fun s₃ ⟨e3, g₃, rd₃, wr₃, m₃⟩ => ?_
  have cs : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r := fun r hr => by
    by_cases h15 : r = .r15
    · subst h15; rw [e3, rdi₂, off_sub, h.r15]
    · rw [g₃ r h15, cs₂ r hr, cs₁ r hr]
  have hf : Frame (macR s₀) s.mem s₃.mem := by rw [m₃]; exact frame_mac' (by omega) (by omega) f₂
  exact ⟨mac_inv hp h cs (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁]) hf, cs, hf,
    fun key msg hr => by rw [m₃]; exact repr₂ key msg hr⟩

theorem finalizeTo_eq (out : Nat) : finalizeTo out =
    .seq (.block ((ptr .rdi .r15 448 ++ ptr .rsi .r15 656 ++ [.mov32 .rdx (.imm 0)]) ++ ptr .rcx .r15 out))
      (.call "vg_poly1305_finalize" Impl.Poly1305.X86_64.finalize) := rfl

/-- The tag written to `ctx[out, out + 16)`. -/
theorem finalizeTo_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) {out : Nat}
    (hout : out + 16 ≤ 448 ∨ (576 ≤ out ∧ out + 16 ≤ 656)) :
    WP isa (finalizeTo out) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.gpr .rdi = off (cx s₀) 448 ∧ s'.gpr .rcx = off (cx s₀) out ∧
      Frame [sub s₀ 448 128, sub s₀ out 16, stkR s₀] s.mem s'.mem ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg → bytesAt s'.mem (off (cx s₀) out) 16 = mac key msg := by
  rw [finalizeTo_eq]
  refine WP.seq (WP.block_append (WP.mono (ptrs_ok 656 (by omega) 0 s)
    fun s₁ ⟨rdi₁, rsi₁, rdx₁, cs₁, rd₁, wr₁, m₁⟩ => ?_))
  refine WP.mono (ptr_ok .rcx .r15 (k := out) (by omega) s₁) fun s₂ ⟨e2, g₂, rd₂, wr₂, m₂⟩ => ?_
  have cs₂' : ∀ r ∈ calleeSaved, s₂.gpr r = s.gpr r := fun r hr => by
    rw [g₂ r (calleeSaved_ne hr).2.1, cs₁ r hr]
  have rsp₂ : s₂.gpr .rsp = s₀.gpr .rsp := by rw [cs₂' _ calleeSaved_rsp, h.rsp]
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, wr₁, h.wr]
  have r15₁ : s₁.gpr .r15 = cx s₀ := by rw [cs₁ _ (by simp [calleeSaved]), h.r15]
  have hrdi : s₂.gpr .rdi = off (cx s₀) 448 := by rw [g₂ _ (by decide), rdi₁, h.r15]
  have hrsi : s₂.gpr .rsi = off (cx s₀) 656 := by rw [g₂ _ (by decide), rsi₁, h.r15]
  have hrdx : s₂.gpr .rdx = BitVec.ofNat 64 0 := by rw [g₂ _ (by decide), rdx₁]; rfl
  have hrcx : s₂.gpr .rcx = off (cx s₀) out := by rw [e2, r15₁]
  have ho : out + 16 ≤ 1024 := by omega
  refine finalize_call hrdi hrsi hrdx hrcx (by omega)
    (sub_disj s₀ (by omega) (by omega) (by omega)) (sub_disj s₀ (by omega) (by omega) ho)
    (sub_disj s₀ (by omega) (by omega) ho)
    (by rw [rsp₂]; exact hp.below8_sub (by omega)) (by rw [rsp₂]; exact hp.below8_sub (by omega))
    (by rw [rsp₂]; exact hp.below8_sub ho)
    (covers_left _ (covers_sub hp wr₂' _ (by
      intro r hr; simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨656, rfl, show 656 + 0 ≤ 1024 by omega⟩
      · exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩
      · exact ⟨out, rfl, ho⟩)))
    (covers_sub hp wr₂' _ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨448, rfl, show 448 + 128 ≤ 1024 by omega⟩
      · exact ⟨out, rfl, ho⟩))
    fun s₃ rd₃ wr₃ cs₃ f₃ rdi₃ rcx₃ tag₃ => ?_
  rw [rsp₂, m₂, m₁] at f₃
  refine ⟨fun r hr => by rw [cs₃ r hr, cs₂' r hr], by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], rdi₃, rcx₃,
    f₃.sub fun r hr => ?_, fun key msg hr => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨sub s₀ 448 128, by simp, fun _ h => h⟩
    · exact ⟨sub s₀ out 16, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, below8_stk s₀⟩
  · have := tag₃ key msg (by rw [m₂, m₁]; exact hr)
    rwa [show bytesAt _ _ 0 = [] from rfl, List.append_nil] at this

end VG.Proof.ChaCha20Poly1305.X86_64
