import VerifiedGarbage.Proof.Argon2.X86.Derive.FillCT1

/-!
# Argon2 on x86 (32-bit): memory initialization, in two runs

`memoryInit_rel`: clearing the matrix and the calls of H′ for the first two
blocks of every lane leak the same trace in two runs with the same public
data: the calls' arguments are H₀'s place in the locals and the blocks'
addresses, which only the lane fixes.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd wp_mov wp_movi wp_addi)
open VG.Spec.Blake2 (bytesAt)
open VG.Impl.Sha512.X86 (at_)
open VG.Impl.Argon2.X86.Derive (argOff columnOff laneWordOff)

/-- The state before block `c` of lane `l`. -/
def IB (s₀ : State) (h0 : List Byte) (l c : Nat) (s : State) : Prop :=
  Inv s₀ s ∧ Prm s₀ s ∧ bytesAt s.mem ((E s₀).setWidth 64) 64 = h0 ∧ s.gpr .esi = BitVec.ofNat 32 l ∧
    s.gpr .edi = memP s₀ + BitVec.ofNat 32 ((l * (prm s₀).laneLen + c) * 1024)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem initBlock_w {h0 : List Byte} {l c : Nat} (hl : l < lanesN s₀) (hc : c < 2) {s : State}
    (h : IB s₀ h0 l c s) : WP isa (Impl.Argon2.X86.Derive.initBlock c) s (IB s₀ h0 l c) :=
  (initBlock_ok hp h.1 h.2.1 h.2.2.1 hl hc h.2.2.2.1 h.2.2.2.2).mono fun _ ⟨i, p, b, e, d, _, _⟩ =>
    ⟨i, p, b, e.trans h.2.2.2.1, d.trans h.2.2.2.2⟩

omit hp in
theorem nextBlock_w {h0 : List Byte} {l : Nat} {s : State} (h : IB s₀ h0 l 0 s) :
    WP isa (.block [.alu .add .edi (.imm 1024)]) s (IB s₀ h0 l 1) :=
  wp_addi fun t u => WP.block_nil ⟨h.1.upd u (by decide) (by decide), h.2.1.of_mem u.mem,
    by rw [u.mem]; exact h.2.2.1, by rw [u.other _ (by decide)]; exact h.2.2.2.1, by
      rw [u.gpr, h.2.2.2.2, show (1024 : BitVec 32) = BitVec.ofNat 32 1024 from rfl, BitVec.add_assoc,
        BitVec.ofNat_add_ofNat, show (l * (prm s₀).laneLen + 0) * 1024 + 1024 = (l * (prm s₀).laneLen + 1) * 1024 by
          rw [Nat.add_mul, Nat.add_mul]]⟩

/-- The instructions before `initBlock`'s call of H′. -/
theorem ibBlk_ok {s : State} (h : Inv s₀ s) (c : Nat) :
    WP isa (.block [.mov .eax (.imm (BitVec.ofNat 32 c)), .store (at_ .ebp columnOff) .eax,
      .store (at_ .ebp laneWordOff) .esi, .mov .eax (.imm 72), .mov .ecx (.imm 1024),
      .mov .edx (Impl.Argon2.X86.Derive.fr (argOff 15))]) s fun t => Inv s₀ t ∧ t.gpr .edx = scrP s₀ ∧
      t.gpr .eax = 72 ∧ t.gpr .ecx = 1024 ∧ t.gpr .edi = s.gpr .edi := by
  refine wp_movi fun s₁ u₁ => ?_
  have i₁ := h.upd u₁ (by decide) (by decide)
  refine wp_stloc hp i₁ (d := 64) (by decide) fun s₂ i₂ _ _ g₂ _ => ?_
  refine wp_stloc hp i₂ (d := 68) (by decide) fun s₃ i₃ _ _ g₃ _ => ?_
  refine wp_movi fun s₄ u₄ => wp_movi fun s₅ u₅ => wp_ldarg hp ((i₃.upd u₄ (by decide) (by decide)).upd u₅
    (by decide) (by decide)) (i := 15) (by decide) fun s₆ u₆ => WP.block_nil
    ⟨((i₃.upd u₄ (by decide) (by decide)).upd u₅ (by decide) (by decide)).upd u₆ (by decide) (by decide),
      u₆.gpr, by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr],
      by rw [u₆.other _ (by decide), u₅.gpr],
      by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), g₃, g₂,
        u₁.other _ (by decide)]⟩

end

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- `initBlock c` leaks the same trace in two runs at the same lane. -/
theorem initBlock_rel {h₁ h₂ : List Byte} {l c : Nat} (hl : l < lanesN s₀₁) (hc : c < 2)
    (hchk : ∃ hc, (VG.Taint.check taint (τB [] []) (.block [.mov .eax (.imm (BitVec.ofNat 32 c)),
      .store (at_ .ebp columnOff) .eax, .store (at_ .ebp laneWordOff) .esi, .mov .eax (.imm 72),
      .mov .ecx (.imm 1024), .mov .edx (Impl.Argon2.X86.Derive.fr (argOff 15))]) hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => IB s₀₁ h₁ l c s₁ ∧ IB s₀₂ h₂ l c s₂) (Impl.Argon2.X86.Derive.initBlock c)
      fun _ _ => True := by
  have pe := T.pb.prm_eq
  have cellF : ∀ {s₀ : State}, DPre s₀ → l < lanesN s₀ →
      (l * (prm s₀).laneLen + c) * 1024 + 1024 ≤ blocksN s₀ * 1024 ∧ l * (prm s₀).laneLen + c < blocksN s₀ :=
    fun {s₀} hp hl => by
      have L2 : 2 ≤ (prm s₀).laneLen := by rw [hp.laneLen_eq]; have := hp.segLen_two; omega
      have : l * (prm s₀).laneLen + c < blocksN s₀ := by
        rw [hp.blocks_eq]
        have := Nat.mul_le_mul_right (prm s₀).laneLen (show l + 1 ≤ lanesN s₀ by omega)
        rw [Nat.succ_mul] at this
        omega
      exact ⟨by omega, this⟩
  have pre : ∀ {s₀ : State}, DPre s₀ → l < lanesN s₀ → ∀ {s t : State}, IB s₀ h₁ l c s ∨ IB s₀ h₂ l c s →
      Inv s₀ t ∧ t.gpr .edx = scrP s₀ ∧ t.gpr .eax = 72 ∧ t.gpr .ecx = 1024 ∧ t.gpr .edi = s.gpr .edi →
      Inv s₀ t ∧ t.gpr .edx = scrP s₀ ∧
        (∃ R ∈ [memR s₀, locR s₀], ∃ off, (t.gpr .ebp).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
          off + (t.gpr .eax).toNat ≤ R.len) ∧ (t.gpr .ebp).toNat + (t.gpr .eax).toNat ≤ 2 ^ 32 ∧
        (∃ R ∈ [memR s₀, outR s₀], ∃ off, (t.gpr .edi).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
          off + (t.gpr .ecx).toNat ≤ R.len) ∧ (t.gpr .edi).toNat + (t.gpr .ecx).toNat ≤ 2 ^ 32 ∧
        1 ≤ (t.gpr .ecx).toNat := fun {s₀} hp hl {s t} hs ⟨i, d, a, c', e⟩ => by
    have hE := E_hi hp
    have hm := hp.mem_fits
    obtain ⟨hc', hk⟩ := cellF hp hl
    have ed : t.gpr .edi = memP s₀ + BitVec.ofNat 32 ((l * (prm s₀).laneLen + c) * 1024) := by
      rw [e]; rcases hs with hs | hs <;> exact hs.2.2.2.2
    have an : (memP s₀ + BitVec.ofNat 32 ((l * (prm s₀).laneLen + c) * 1024)).toNat =
        (memP s₀).toNat + (l * (prm s₀).laneLen + c) * 1024 := add_nat (by omega)
    refine ⟨i, d, ⟨locR s₀, by simp, 0, by rw [i.ebp]; simp, by rw [a]; show 0 + 72 ≤ 144; decide⟩,
      by rw [i.ebp, a]; show (E s₀).toNat + 72 ≤ 2 ^ 32; omega,
      ⟨memR s₀, by simp, (l * (prm s₀).laneLen + c) * 1024, by rw [ed, cell_addr hp hk]; rfl,
        by rw [c']; exact hc'⟩, by rw [ed, c', an]; show _ + 1024 ≤ 2 ^ 32; omega,
      by rw [c']; decide⟩
  unfold Impl.Argon2.X86.Derive.initBlock Impl.Argon2.X86.Derive.hPrimeCall
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) hchk)
    (G₁ := fun t => ∃ s, IB s₀₁ h₁ l c s ∧ Inv s₀₁ t ∧ t.gpr .edx = scrP s₀₁ ∧ t.gpr .eax = 72 ∧
      t.gpr .ecx = 1024 ∧ t.gpr .edi = s.gpr .edi)
    (G₂ := fun t => ∃ s, IB s₀₂ h₂ l c s ∧ Inv s₀₂ t ∧ t.gpr .edx = scrP s₀₂ ∧ t.gpr .eax = 72 ∧
      t.gpr .ecx = 1024 ∧ t.gpr .edi = s.gpr .edi)
    (fun s h => (ibBlk_ok T.hp₁ h.1 c).mono fun t ht => ⟨s, h, ht⟩)
    (fun s h => (ibBlk_ok T.hp₂ h.1 c).mono fun t ht => ⟨s, h, ht⟩) ?_
  refine T.hcall_rel (r := .ebp) (by decide) fun s₁ s₂ ⟨a₁, g₁, k₁⟩ ⟨a₂, g₂, k₂⟩ =>
    ⟨pre T.hp₁ hl (.inl g₁) k₁, pre T.hp₂ (T.pb.lanesN_eq ▸ hl) (.inr g₂) k₂, ?_, ?_, ?_, ?_⟩
  · rw [k₁.1.ebp, k₂.1.ebp, T.pb.E]
  · rw [k₁.2.2.1, k₂.2.2.1]
  · rw [k₁.2.2.2.2, k₂.2.2.2.2, g₁.2.2.2.2, g₂.2.2.2.2, pe, T.pb.memP_eq]
  · rw [k₁.2.2.2.1, k₂.2.2.2.1]

/-- `initLane` leaks the same trace in two runs at the same lane. -/
theorem initLane_rel {h₁ h₂ : List Byte} {l : Nat} (hl : l < lanesN s₀₁) :
    RelCT isa (fun s₁ s₂ => LI s₀₁ h₁ l s₁ ∧ LI s₀₂ h₂ l s₂) Impl.Argon2.X86.Derive.initLane fun _ _ => True := by
  have hl₂ : l < lanesN s₀₂ := T.pb.lanesN_eq ▸ hl
  have ib : ∀ {s₀ s : State} {h0 : List Byte}, LI s₀ h0 l s → IB s₀ h0 l 0 s := fun h =>
    ⟨h.inv, h.pr, h.b0, h.esi, by rw [Nat.add_zero]; exact h.edi⟩
  unfold Impl.Argon2.X86.Derive.initLane
  refine (RelCT.seqW (T.initBlock_rel hl (by decide) ⟨_, by taint_decide⟩) (fun s h => initBlock_w T.hp₁ hl (by decide) h)
    (fun s h => initBlock_w T.hp₂ hl₂ (by decide) h) ?_).mono (fun _ _ h => ⟨ib h.1, ib h.2⟩) fun _ _ h => h
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => nextBlock_w h) (fun s h => nextBlock_w h) ?_
  refine RelCT.seqW (T.initBlock_rel hl (by decide) ⟨_, by taint_decide⟩) (fun s h => initBlock_w T.hp₁ hl (by decide) h)
    (fun s h => initBlock_w T.hp₂ hl₂ (by decide) h) ?_
  exact T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩

/-- `memoryInit` leaks the same trace in two runs. -/
theorem memoryInit_rel {h₁ h₂ : List Byte} :
    RelCT isa (fun s₁ s₂ => (Inv s₀₁ s₁ ∧ Prm s₀₁ s₁ ∧ bytesAt s₁.mem ((E s₀₁).setWidth 64) 64 = h₁) ∧
      (Inv s₀₂ s₂ ∧ Prm s₀₂ s₂ ∧ bytesAt s₂.mem ((E s₀₂).setWidth 64) 64 = h₂))
      Impl.Argon2.X86.Derive.memoryInit fun _ _ => True := by
  have le := T.pb.lanesN_eq
  have hl1 := T.hp₁.lanes_pos
  unfold Impl.Argon2.X86.Derive.memoryInit
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => clearW_ok T.hp₁ h.1 h.2.1 h.2.2) (fun s h => clearW_ok T.hp₂ h.1 h.2.1 h.2.2) ?_
  refine RelCT.seqW (T.leafI [] (fun s₁ s₂ h => ⟨h.1.1, h.2.1, by simp⟩) ⟨_, by taint_decide⟩)
    (fun s h => laneStart_ok T.hp₁ h) (fun s h => laneStart_ok T.hp₂ h) ?_
  generalize hN : lanesN s₀₁ = N at hl1
  have hN₂ : lanesN s₀₂ = N := by rw [← le, hN]
  refine (RelCT.loop (Q := fun _ _ => True) (fun n s₁ s₂ => ∃ l, n = N - l ∧ l < N ∧
      LI s₀₁ h₁ l s₁ ∧ LI s₀₂ h₂ l s₂) ?step N).mono (fun s₁ s₂ h => ?init) fun _ _ h => h
  case init => exact ⟨0, by omega, hl1, h.1, h.2⟩
  intro n s₁ s₂ t₁ t₂ s₁' s₂' ⟨l, hn, hl, g₁, g₂⟩ e₁ e₂
  obtain ⟨ht, ⟨k₁, c₁⟩, ⟨k₂, c₂⟩⟩ := HPrime.rel_wp (T.initLane_rel (by rw [hN]; exact hl))
    (fun s h => lane_ok T.hp₁ (by rw [hN]; exact hl) h) (fun s h => lane_ok T.hp₂ (by rw [hN₂]; exact hl) h)
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨g₁, g₂⟩ e₁ e₂
  rw [hN] at c₁
  rw [hN₂] at c₂
  refine ⟨ht, by show s₁'.cf = s₂'.cf; rw [c₁, c₂], fun _ => trivial, fun hc => ?_⟩
  have e : l + 1 < N := by
    rw [show isa.eval .b s₁' = s₁'.cf from rfl, c₁] at hc
    simpa using hc
  exact ⟨N - (l + 1), by omega, l + 1, rfl, e, k₁, k₂⟩

end Two

end VG.Proof.Argon2.X86.Derive
