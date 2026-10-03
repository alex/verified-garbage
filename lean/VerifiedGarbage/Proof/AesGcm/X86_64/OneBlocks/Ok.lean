import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Piece

/-!
# AES-GCM on x86-64: `oneBlocks`

Untrusted: everything here is checked by Lean. `oneBlocks` encrypts
(`oneBlocksE_ok`) or decrypts (`oneBlocksD_ok`) the `⌊n / 16⌋` whole blocks
of the data and absorbs them, from the counter block and the accumulator of
the state, and keeps what is left of the data.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith ctr32 ghashFrom inc32)

/-- The counter block and the accumulator, in the state. -/
abbrev cbA (W : Addr) : Addr := W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48
abbrev yA (W : Addr) : Addr := W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- The length kept, apart from what the call reads. -/
theorem w192_eqs {R : Nat} {D : Addr} {n : Nat} {s : State} (h : ObPre Ctx W SP R D n s) (v : BitVec 64) :
    let m := s.mem.writeW (W + BitVec.ofNat 64 192) v
    m.readW (W + BitVec.ofNat 64 176) 64 = s.mem.readW (W + BitVec.ofNat 64 176) 64 ∧
    m.readW (W + BitVec.ofNat 64 200) 64 = s.mem.readW (W + BitVec.ofNat 64 200) 64 ∧
    m.readW (W + BitVec.ofNat 64 208) 64 = s.mem.readW (W + BitVec.ofNat 64 208) 64 ∧
    bytesAt m Ctx (16 * (R + 1)) = bytesAt s.mem Ctx (16 * (R + 1)) ∧
    blockAt m (cbA W) = blockAt s.mem (cbA W) ∧ blockAt m (yA W) = blockAt s.mem (yA W) ∧
    blocksAt m D (n / 16) = blocksAt s.mem D (n / 16) ∧ blockAt m (Ctx + 240) = blockAt s.mem (Ctx + 240) ∧
    Frame [⟨W + BitVec.ofNat 64 192, 24⟩] s.mem m := by
  intro m
  have ww := L.ww
  have hf : Frame [⟨W + BitVec.ofNat 64 192, 8⟩] s.mem m :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have sep : ∀ d, d + 8 ≤ 192 ∨ 200 ≤ d → d + 8 ≤ 2560 →
      Mem.Sep (W + BitVec.ofNat 64 d) (64 / 8) (W + BitVec.ofNat 64 192) (64 / 8) :=
    fun d h₁ h₂ => Offset.sep _ (by omega) (by omega) (by omega)
  have one : ∀ {r : Region}, r.Disjoint ⟨W + BitVec.ofNat 64 192, 8⟩ →
      ∀ r' ∈ [(⟨W + BitVec.ofNat 64 192, 8⟩ : Region)], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  have hRb : 16 * (R + 1) ≤ 256 := by rcases h.rounds.2 with h | h | h <;> subst h <;> decide
  refine ⟨Mem.readW_writeW_sep (sep 176 (.inl (by decide)) (by decide)) (by decide),
    Mem.readW_writeW_sep (sep 200 (.inr (by decide)) (by decide)) (by decide),
    Mem.readW_writeW_sep (sep 208 (.inr (by decide)) (by decide)) (by decide),
    bytesAt_frame hf (one ((L.cw'.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))))
      (by have := L.cw; omega),
    blockAt_frame hf (one (by simp only [cbA, yA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide))),
    blockAt_frame hf (one (by simp only [cbA, yA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide))),
    blocksAt_frame hf (one ((h.data.ok.w.sub_left (Region.sub_prefix (by omega))).sub_right
      (Lay.wSub (by decide)))) (by have := h.data.ok.wrap; omega),
    blockAt_frame hf (one ((L.cw'.sub_left (Offset.sub_base (d := 240) _ (by decide))).sub_right
      (Lay.wSub (by decide)))),
    hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩⟩

/-- The bookkeeping of `oneBlocks` around its call: from the state `s₁` after
the length is kept to the end, given the call's frame (`hframe`). -/
theorem oneBlocks_core (f : Fn) {R : Nat} {D : Addr} {n : Nat} {s : State} (h : ObPre Ctx W SP R D n s)
    {Out : State → State → Prop}
    (hframe : ∀ s₂, ObIn Ctx W SP R D n (n / 16) s₂ →
      WP isa (.frame (.push [.rax]) (.call f.name f.code) (.pop .rax 1)) s₂ fun s₄ =>
        (∀ r ∈ calleeSaved, s₄.gpr r = s₂.gpr r) ∧ s₄.rd = s₂.rd ∧ s₄.wr = s₂.wr ∧
        Frame (obFrame W SP D (n / 16)) s₂.mem s₄.mem ∧ Out s₂ s₄)
    (h0 : n / 16 = 0 → ∀ s₁, s₁.mem = s.mem.writeW (W + BitVec.ofNat 64 192) (BitVec.ofNat 64 n) → Out s s₁)
    (hout : ∀ s₂ s₄ s₅, s₂.mem = s.mem.writeW (W + BitVec.ofNat 64 192) (BitVec.ofNat 64 n) → Out s₂ s₄ →
      Frame [⟨W + BitVec.ofNat 64 200, 16⟩] s₄.mem s₅.mem → Out s s₅) :
    WP isa (oneBlocks f) s fun s' => ObPost Ctx W SP D n s s' ∧ Out s s' := by
  have hn : n < 2 ^ 64 := h.data.ok.lt
  have he := h.env
  obtain ⟨e176, e200, e208, -, -, -, -, -, f192⟩ := w192_eqs L h (BitVec.ofNat 64 n)
  refine WP.seq (WP.mono (ob1_ok hn he h.len) fun s₁ ⟨r₁, z₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) rd₁ wr₁
  have t₁ : s₁.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n := by rw [m₁, Mem.readW_writeW_self64]
  have hf₁ : Frame (⟨W + BitVec.ofNat 64 192, 24⟩ :: obFrame W SP D (n / 16)) s.mem s₁.mem := by
    rw [m₁]; exact f192.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..
  refine WP.ite (decide (n / 16 = 0)) (by simp only [eval, z₁]) (fun hz => ?_) (fun hz => ?_)
  · simp only [decide_eq_true_eq] at hz
    refine WP.block_nil ⟨⟨he₁, rd₁, wr₁, hf₁, t₁, ?_, ?_⟩, h0 hz s₁ m₁⟩
    · rw [m₁, e200, h.dat, hz]; simp
    · rw [m₁, e208, h.len]; congr 1; omega
  · simp only [decide_eq_false_iff_not] at hz
    have hR₁ : RoundsAt s₁.mem W R := ⟨by rw [m₁, e176]; exact h.rounds.1, h.rounds.2⟩
    have hd₁ : s₁.mem.readW (W + BitVec.ofNat 64 200) 64 = D := by rw [m₁, e200, h.dat]
    refine WP.seq (WP.mono (ob2_ok he₁ hR₁ hd₁) fun s₂ ⟨a1, a2, a3, a4, a5, a6, a7, g₂, m₂, rd₂, wr₂⟩ => ?_)
    have he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)) rd₂ wr₂
    have obi : ObIn Ctx W SP R D n (n / 16) s₂ := ⟨he₂, h.data.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁),
      by omega, h.t_c, h.t_w, h.t_d, h.sp24, a1, a2, a3, a4, a5, by rw [a6, r₁], a7, h.rounds.2⟩
    refine WP.seq (WP.mono (hframe s₂ obi) fun s₄ ⟨cs₄, rd₄, wr₄, fr₄, o₄⟩ => ?_)
    have he₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ := he₂.keep (fun r hr => cs₄ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])) rd₄ wr₄
    have kp : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
        s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
      rw [fr₄.readW (Region.contains_self _ _) (ob_slots L h.data.ok.w (by omega) h.t_w h₁ h₂) (by decide), m₂]
    have hd₄ : s₄.mem.readW (W + BitVec.ofNat 64 200) 64 = D := by rw [kp 200 (by decide) (by decide), hd₁]
    have hl₄ : s₄.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n := by
      rw [kp 208 (by decide) (by decide), m₁, e208, h.len]
    refine WP.mono (ob3_ok hn he₄ hd₄ hl₄) fun s₅ ⟨g₅, d₅, l₅, f₅, rd₅, wr₅⟩ => ?_
    have he₅ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₅ := he₄.keep (fun r hr => g₅ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) rd₅ wr₅
    refine ⟨⟨he₅, rd₅.trans (rd₄.trans (rd₂.trans rd₁)), wr₅.trans (wr₄.trans (wr₂.trans wr₁)), ?_, ?_, d₅, l₅⟩,
      hout s₂ s₄ s₅ (m₂.trans m₁) o₄ f₅⟩
    · refine hf₁.trans ?_
      rw [← m₂]
      refine (fr₄.mono fun r hr => List.mem_cons_of_mem _ hr).trans ?_
      exact f₅.sub fun r hr => ⟨_, List.mem_cons_self .., by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by decide) (by decide)⟩
    · rw [f₅.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (.inl (by decide)) (by decide) (by decide)) (by decide),
        kp 192 (by decide) (by decide), t₁]


/-- What encrypting the whole blocks does, from `s` to `s'`. -/
def OutE (Ctx W : Addr) (R : Nat) (D : Addr) (q : Nat) (s s' : State) : Prop :=
  blocksAt s'.mem D q = ctr32 (aesWith R (bytesAt s.mem Ctx (16 * (R + 1)))) (blockAt s.mem (cbA W))
    (blocksAt s.mem D q) ∧
  blockAt s'.mem (cbA W) = Nat.repeat inc32 q (blockAt s.mem (cbA W)) ∧
  blockAt s'.mem (yA W) = ghashFrom (blockAt s.mem (Ctx + 240)) (blockAt s.mem (yA W)) (blocksAt s'.mem D q)

/-- What decrypting the whole blocks does, from `s` to `s'`. -/
def OutD (Ctx W : Addr) (R : Nat) (D : Addr) (q : Nat) (s s' : State) : Prop :=
  blocksAt s'.mem D q = ctr32 (aesWith R (bytesAt s.mem Ctx (16 * (R + 1)))) (blockAt s.mem (cbA W))
    (blocksAt s.mem D q) ∧
  blockAt s'.mem (cbA W) = Nat.repeat inc32 q (blockAt s.mem (cbA W)) ∧
  blockAt s'.mem (yA W) = ghashFrom (blockAt s.mem (Ctx + 240)) (blockAt s.mem (yA W)) (blocksAt s.mem D q)

/-- The kept slots written after the call are apart from the blocks, the
counter block and the accumulator. -/
theorem ob_after {R : Nat} {D : Addr} {n : Nat} {s : State} (h : ObPre Ctx W SP R D n s) {m m' : Mem}
    (hf : Frame [⟨W + BitVec.ofNat 64 200, 16⟩] m m') :
    blocksAt m' D (n / 16) = blocksAt m D (n / 16) ∧ blockAt m' (cbA W) = blockAt m (cbA W) ∧
    blockAt m' (yA W) = blockAt m (yA W) := by
  have one : ∀ {r : Region}, r.Disjoint ⟨W + BitVec.ofNat 64 200, 16⟩ →
      ∀ r' ∈ [(⟨W + BitVec.ofNat 64 200, 16⟩ : Region)], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  refine ⟨blocksAt_frame hf (one ((h.data.ok.w.sub_left (Region.sub_prefix (by omega))).sub_right
      (Lay.wSub (by decide)))) (by have := h.data.ok.wrap; omega),
    blockAt_frame hf (one (by simp only [cbA, yA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide))),
    blockAt_frame hf (one (by simp only [cbA, yA]; rw [add_ofNat_assoc]; exact L.w_w (.inl (by decide)) (by decide) (by decide)))⟩

/-- `oneBlocks` of the encrypting function. -/
theorem oneBlocksE_ok (v : GcmImpl) {R : Nat} {D : Addr} {n : Nat} {s : State} (h : ObPre Ctx W SP R D n s) :
    WP isa (oneBlocks v.callees.enc) s fun s' => ObPost Ctx W SP D n s s' ∧ OutE Ctx W R D (n / 16) s s' := by
  obtain ⟨-, -, -, eK, eC, eY, eB, eH, -⟩ := w192_eqs L h (BitVec.ofNat 64 n)
  refine oneBlocks_core L _ h (fun s₂ hi => obFrameE_ok L v hi) (fun hz s₁ m₁ => ?_) (fun s₂ s₄ s₅ m₂ o f => ?_)
  · rw [OutE, hz, m₁, eC, eY]; exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨a₁, a₂, a₃⟩ := ob_after L h f
    obtain ⟨o₁, o₂, o₃⟩ := o
    simp only [m₂, eK, eC, eB, eY, eH] at o₁ o₂ o₃
    exact ⟨a₁.trans o₁, a₂.trans o₂, by rw [a₃, a₁]; exact o₃⟩

/-- `oneBlocks` of the decrypting function. -/
theorem oneBlocksD_ok (v : GcmImpl) {R : Nat} {D : Addr} {n : Nat} {s : State} (h : ObPre Ctx W SP R D n s) :
    WP isa (oneBlocks v.callees.dec) s fun s' => ObPost Ctx W SP D n s s' ∧ OutD Ctx W R D (n / 16) s s' := by
  obtain ⟨-, -, -, eK, eC, eY, eB, eH, -⟩ := w192_eqs L h (BitVec.ofNat 64 n)
  refine oneBlocks_core L _ h (fun s₂ hi => obFrameD_ok L v hi) (fun hz s₁ m₁ => ?_) (fun s₂ s₄ s₅ m₂ o f => ?_)
  · rw [OutD, hz, m₁, eC, eY]; exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨a₁, a₂, a₃⟩ := ob_after L h f
    obtain ⟨o₁, o₂, o₃⟩ := o
    simp only [m₂, eK, eC, eB, eY, eH] at o₁ o₂ o₃
    exact ⟨a₁.trans o₁, a₂.trans o₂, by rw [a₃]; exact o₃⟩

end

end VG.Proof.AesGcm.X86_64
