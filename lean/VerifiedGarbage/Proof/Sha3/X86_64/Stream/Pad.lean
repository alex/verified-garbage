import VerifiedGarbage.Proof.Sha3.X86_64.Call

/-!
# SHA-3 on x86-64: `pad`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Sha3.X86_64.Stream.Pad

open VG VG.X86_64 VG.Impl.Sha3.X86_64.Stream
open VG.Spec.Sha3 (stateAt keccakF absorb pad rates Repr)
open VG.Proof.Sha3 (xorByte Rep stateAt_xorByte absorb_pad)

theorem writeW8_apply (m : Mem) (a x : Addr) (v : BitVec 8) :
    m.writeW a v x = if x = a then v else m x := by
  simp only [Mem.writeW, Mem.write]
  by_cases h : x = a
  · subst h; simp
  · have : ¬ (x - a).toNat < 8 / 8 := by
      intro h'; apply h; bv_omega
    simp only [this, ite_false, h]

theorem xor_byte (b : BitVec 8) (v : BitVec 64) :
    (b.setWidth 64 ^^^ v).setWidth 8 = b ^^^ v.setWidth 8 := by
  ext i _; simp

theorem xor_0x80 (b : BitVec 8) :
    (b.setWidth 64 ^^^ (0x80 : BitVec 32).signExtend 64).setWidth 8 = b ^^^ 0x80 := by
  rw [xor_byte]; rfl

theorem rate_bounds {r : Nat} (h : r ∈ rates) : 72 ≤ r ∧ r ≤ 168 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h
  omega

theorem ne_of_lt200 {p : Addr} {a b : Nat} (ha : a < 200) (hb : b < 200) (h : a ≠ b) :
    p + BitVec.ofNat 64 a ≠ p + BitVec.ofNat 64 b := by
  intro e; apply h; bv_omega

theorem ret_below (sp : Addr) : Region.Disjoint ⟨sp, 8⟩ (below sp 8) := by
  intro x h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

theorem correct {s₀ : State} (hp : Proof.Sha3.padX86_64.pre s₀) :
    WP isa Impl.Sha3.X86_64.Stream.pad s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha3.padX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, d_ss, d_rs, d_rc, d_ks, d_kc, hrate, hpos⟩ := hp
  have hr := rate_bounds hrate
  set st := s₀.gpr .rdi with hst
  set scr := s₀.gpr .r8 with hscr
  set rate := (s₀.gpr .rsi).toNat with hrate'
  set pos := (s₀.gpr .rdx).toNat with hpos'
  have hin : ∀ j < 200, (⟨st, 200⟩ : Region).Contains (st + BitVec.ofNat 64 j) 1 := fun j hj =>
    Proof.Sha3.X86_64.contains_offset (by omega) (by omega)
  have hw : ∀ j < 200, InRegions s₀.wr (st + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hwr]; exact ⟨_, List.mem_cons_self .., hin j hj⟩
  have hw' : ∀ j < 200, InRegions (s₀.rd ++ s₀.wr) (st + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hrd]; exact hw j hj
  have e₁ : s₀.ea { base := .rdi, index := some .rdx, scale := 1 } = st + BitVec.ofNat 64 pos := by
    simp only [State.ea, BitVec.mul_one, hpos', BitVec.ofNat_toNat, BitVec.setWidth_eq, ← hst]
    simp
  have e₂ : s₀.ea { base := .rdi, index := some .rsi, scale := 1, disp := -1 } =
      st + BitVec.ofNat 64 (rate - 1) := by
    simp only [State.ea, BitVec.mul_one, ← hst]
    bv_omega
  unfold Impl.Sha3.X86_64.Stream.pad
  refine WP.seq (wp_movzx8 e₁ (hw' _ (by omega)) fun s₁ u₁ => wp_xor fun s₂ u₂ =>
    wp_store8 (a := st + BitVec.ofNat 64 pos) ?_ ?_ fun s₃ g₃ m₃ rd₃ wr₃ => ?_)
  · rw [← e₁]; simp only [State.ea, u₂.other _ (by decide : Reg.rdi ≠ .rax),
      u₁.other _ (by decide : Reg.rdi ≠ .rax), u₂.other _ (by decide : Reg.rdx ≠ .rax),
      u₁.other _ (by decide : Reg.rdx ≠ .rax)]
  · rw [u₂.wr, u₁.wr]; exact hw _ (by omega)
  have k₃ : ∀ r, r ≠ .rax → s₃.gpr r = s₀.gpr r := fun r h => by rw [g₃, u₂.other _ h, u₁.other _ h]
  refine wp_movzx8 (a := st + BitVec.ofNat 64 (rate - 1)) ?_
    (by rw [rd₃, wr₃, u₂.rd, u₁.rd, u₂.wr, u₁.wr]; exact hw' _ (by omega))
    fun s₄ u₄ => wp_xori fun s₅ u₅ => wp_store8 (a := st + BitVec.ofNat 64 (rate - 1)) ?_ ?_
    fun s₆ g₆ m₆ rd₆ wr₆ => wp_mov fun s₇ u₇ => wp_nil ?_
  · rw [← e₂]; simp only [State.ea, k₃ _ (by decide : Reg.rdi ≠ .rax), k₃ _ (by decide : Reg.rsi ≠ .rax)]
  · rw [← e₂]; simp only [State.ea, u₅.other _ (by decide : Reg.rdi ≠ .rax),
      u₄.other _ (by decide : Reg.rdi ≠ .rax), u₅.other _ (by decide : Reg.rsi ≠ .rax),
      u₄.other _ (by decide : Reg.rsi ≠ .rax), k₃ _ (by decide : Reg.rdi ≠ .rax),
      k₃ _ (by decide : Reg.rsi ≠ .rax)]
  · rw [u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr]; exact hw _ (by omega)
  -- The two bytes written.
  have hb₁ : s₃.mem = s₀.mem.writeW (st + BitVec.ofNat 64 pos)
      (s₀.mem (st + BitVec.ofNat 64 pos) ^^^ (s₀.gpr .rcx).setWidth 8) := by
    rw [m₃, u₂.gpr, u₁.gpr, u₁.other _ (by decide), u₂.mem, u₁.mem, xor_byte]
  have hb₂ : s₆.mem = s₃.mem.writeW (st + BitVec.ofNat 64 (rate - 1))
      (s₃.mem (st + BitVec.ofNat 64 (rate - 1)) ^^^ 0x80) := by
    rw [m₆, u₅.gpr, u₄.gpr, u₅.mem, u₄.mem, xor_0x80]
  have hS : stateAt s₆.mem st =
      xorByte (xorByte (stateAt s₀.mem st) pos ((s₀.gpr .rcx).setWidth 8)) (rate - 1) 0x80 := by
    rw [← stateAt_xorByte (m := s₀.mem) (m' := s₃.mem) (by omega)
      (by simp only [hb₁, writeW8_apply, ↓reduceIte])
      (fun i hi hne => by simp only [hb₁, writeW8_apply, ne_of_lt200 hi (by omega) hne, ite_false])]
    exact stateAt_xorByte (by omega) (by simp only [hb₂, writeW8_apply, ↓reduceIte])
      (fun i hi hne => by simp only [hb₂, writeW8_apply, ne_of_lt200 hi (by omega) hne, ite_false])
  have hf₆ : Frame [⟨st, 200⟩] s₀.mem s₆.mem := by
    rw [hb₂, hb₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hin _ (by omega))).writeW
      (List.mem_singleton_self _) _ (hin _ (by omega))
  have k₇ : ∀ r, r ≠ .rax → r ≠ .rsi → s₇.gpr r = s₀.gpr r := fun r h h' => by
    rw [u₇.other _ h', g₆, u₅.other _ h, u₄.other _ h, k₃ _ h]
  have d₁ : Region.Disjoint ⟨st, 200⟩ ⟨scr, 512⟩ := d_ss.sub_right (Region.sub_prefix (base := scr) (len := 512) (len' := 640) (by omega))
  have hsp₇ : s₇.gpr .rsp = s₀.gpr .rsp := k₇ _ (by decide) (by decide)
  have hbl : below (s₀.gpr .rsp) 8 = ⟨s₀.gpr .rsp - 8, 8⟩ := rfl
  refine call_ok (st := st) (scr := scr) (by rw [k₇ _ (by decide) (by decide)])
    (by rw [u₇.gpr, g₆, u₅.other _ (by decide), u₄.other _ (by decide), k₃ _ (by decide)]) d₁
    (by rw [hsp₇, hbl]; exact d_ks) (by rw [hsp₇, hbl]; exact d_kc.sub_right (Region.sub_prefix (base := scr) (len := 512) (len' := 640) (by omega)))
    (fun a n h => by
      rw [u₇.wr, wr₆, u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr, hwr]
      obtain ⟨r, hr, hc⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., hc⟩
      · exact ⟨⟨scr, 640⟩, by simp, by simp only [Region.Contains] at hc ⊢; omega⟩) ?_
  intro s' _ _ cs' f' e' _ _
  rw [u₇.mem] at f' e'
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun msg hR hm => ?_⟩
  · rw [cs' r hr, k₇ r (fun h => by subst h; simp [calleeSaved] at hr)
      (fun h => by subst h; simp [calleeSaved] at hr)]
  · rw [hsp₇] at f'
    have hf : Frame [⟨st, 200⟩, ⟨scr, 512⟩, below (s₀.gpr .rsp) 8] s₀.mem s'.mem :=
      (hf₆.mono fun r hr => by simp at hr; simp [hr]).trans f'
    exact hf.readW (Region.contains_self _ _) (by
      simpa using ⟨d_rs, d_rc.sub_right (Region.sub_prefix (base := scr) (len := 512) (len' := 640) (by omega)), ret_below _⟩) (by decide)
  · rw [e', hS, absorb_pad (by omega) (by omega), ← hm, show Rep rate msg = stateAt s₀.mem st from hR.symm]

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 136 | .r8 => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x3000, 640⟩]

theorem pad_verified : Verified X86_64.target Impl.Sha3.X86_64.Stream.pad Proof.Sha3.padX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct hs
    exact ⟨t, s', he, h⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .r8, .rsp]) ?_
      (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨sat, rfl, rfl, ?_, ?_, ?_, ?_, ?_, by decide, by decide⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, sat] at h₁ h₂
      bv_omega

end VG.Proof.Sha3.X86_64.Stream.Pad
