import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddSetup
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMain

/-! Full-width multiply-add followed by subgroup reduction. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.X25519.X86_64
open VG.Proof.X25519.X86_64
open VG.Spec.Ed25519 (bytesAt decodeLE)

def scalarMulAddLocal : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rsi, 32⟩, ⟨s.gpr .rdx, 32⟩, ⟨s.gpr .rcx, 32⟩] ∧
    s.wr = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .r8, 8192⟩] ∧
    (⟨s.gpr .rsi, 32⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩ ∧
    (⟨s.gpr .rdx, 32⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩ ∧
    (⟨s.gpr .rcx, 32⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 32⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩ ∧
    (s.gpr .r8).toNat + 8192 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rdi, 32⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩
  post s t := bytesAt t.mem (s.gpr .rdi) 32 = Spec.Ed25519.scalarMulAdd
    (bytesAt s.mem (s.gpr .rsi) 32) (bytesAt s.mem (s.gpr .rdx) 32) (bytesAt s.mem (s.gpr .rcx) 32)
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧
    s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx ∧
    s.gpr .rcx = t.gpr .rcx ∧ s.gpr .r8 = t.gpr .r8

theorem MulAddPre.of {s : State} (h : scalarMulAddLocal.pre s) : MulAddPre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

theorem scalarMulAdd_correct {s : State} (hs : MulAddPre s) :
    WP isa scalarMulAdd s fun t => gprPreserved s t ∧ scalarMulAddLocal.post s t := by
  have hw : (⟨s.gpr .r8, 8192⟩ : Region) ∈ s.wr := by rw [hs.wr]; simp
  rw [scalarMulAdd]
  refine WP.seq (WP.mono (mulAddSetup_ok hs) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (wideAccumulate8192_ok h₁.base (h₁.wr ▸ hw) hs.nowrap
    (by decide) (by decide)) fun s₂ ⟨v₂, k₂⟩ => ?_)
  have prod₂ : wideValue s₂ = fe s.mem (s.gpr .rsi) 0 +
      fe s.mem (s.gpr .rdx) 0 * fe s.mem (s.gpr .rcx) 0 := by
    rw [v₂, h₁.value, h₁.left, h₁.right]
  have base₂ : s₂.gpr .rdi = s.gpr .r8 := (k₂.1 _ (by decide)).trans h₁.base
  have wr₂ : s₂.wr = s.wr := k₂.2.2.2.trans h₁.wr
  apply WP.seq
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (storeWide_ok base₂ (wr₂ ▸ hw)) fun s₃ ⟨v₃, g₃, rd₃, wr₃, o₃⟩ => ?_
  have rdi₃ : s₃.gpr .rdi = s.gpr .r8 := (congrFun g₃ _).trans base₂
  rw [WP.block_append_iff]
  refine WP.mono (reduceArgs_ok rdi₃ (by rw [wr₃, wr₂]; exact hw))
    fun s₄ ⟨rsi₄, m₄, g₄, rd₄, wr₄⟩ => ?_
  refine WP.mono (scalarInit_ok s₄) fun s₅ ⟨b₅, v₅, k₅⟩ => ?_
  have rsi₅ : s₅.gpr .rsi = off (s.gpr .r8) 128 := by rw [k₅.1 _ (by decide), rsi₄]
  have rdi₅ : s₅.gpr .rdi = s.gpr .r8 := by rw [k₅.1 _ (by decide), g₄ _ (by decide), rdi₃]
  have mem₅ : s₅.mem = s₃.mem.writeW (off (s.gpr .r8) 48) (s₃.gpr .rbx) := by rw [k₅.2.1, m₄]
  have o₅ : Outside (s.gpr .r8) 48 8 s₃.mem s₅.mem := by
    rw [mem₅]; exact writeW_outside _ _ _ (by omega)
  have wr₅ : s₅.wr = s.wr := by rw [k₅.2.2.2, wr₄, wr₃, wr₂]
  have read₅ : ∀ k < 8, InRegions (s₅.rd ++ s₅.wr) (s₅.gpr .rsi + BitVec.ofNat 64 (8 * k)) 8 := by
    intro k hk
    refine ⟨⟨s.gpr .r8, 8192⟩, List.mem_append_right _ (wr₅ ▸ hw), ?_⟩
    rw [rsi₅, Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)
  have fm₅ : Frame [⟨s.gpr .r8, 8192⟩] s.mem s₅.mem := by
    have fm₂ : Frame [⟨s.gpr .r8, 8192⟩] s.mem s₂.mem := by rw [k₂.2.1]; exact h₁.frame
    exact (fm₂.trans (scratchFrame o₃ (by decide))).trans (scratchFrame o₅ (by decide))
  have sv₅ : Saved (s.gpr .r8) s.gpr s₅.mem := by
    have sv₂ : Saved (s.gpr .r8) s.gpr s₂.mem := by rw [k₂.2.1]; exact h₁.saved
    exact (sv₂.outside o₃ (by decide)).outside o₅ (by decide)
  have wide₅ : decodeLE (bytesAt s₅.mem (off (s.gpr .r8) 128) 64) = wideValue s₂ := by
    rw [decodeLE_wide, o₅.fe (by decide) (by decide), o₅.fe (by decide) (by decide), ← decodeLE_wide, v₃]
  apply WP.seq
  refine WP.mono (scalarLoop_ok s₅ b₅ v₅ read₅) fun s₆ ⟨v₆, k₆⟩ => ?_
  have wr₆ : s₆.wr = s.wr := k₆.2.2.2.trans wr₅
  have val₆ : scalarValue s₆ = (fe s.mem (s.gpr .rsi) 0 +
      fe s.mem (s.gpr .rdx) 0 * fe s.mem (s.gpr .rcx) 0) % Spec.Ed25519.L := by
    rw [v₆, rsi₅, wide₅, prod₂]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (finishArgs_ok ((k₆.1 _ (by decide)).trans rdi₅) (wr₆ ▸ hw))
    fun s₇ ⟨dx₇, di₇, g₇', m₇', rd₇', wr₇'⟩ => ?_
  have out₇ : s₇.gpr .rdi = s.gpr .rdi := by
    rw [di₇, k₆.2.1, mem₅, Mem.readW_writeW_self64, g₃, k₂.1 _ (by decide), h₁.out]
  refine WP.mono (scalarRestore_ok (g := s.gpr) dx₇ (by rw [wr₇', wr₆]; exact hw)
    (by rw [m₇', k₆.2.1]; exact sv₅)) fun s₈ ⟨rest₈, g₈, m₈, _, wr₈⟩ => ?_
  have rdi₈ : s₈.gpr .rdi = s.gpr .rdi := (g₈ _ (by decide)).trans out₇
  have hwo : (⟨s.gpr .rdi, 32⟩ : Region) ∈ s₈.wr := by rw [wr₈, wr₇', wr₆, hs.wr]; simp
  refine WP.mono (scalarOut_ok rdi₈ hwo) fun t ⟨mt, gt, _, _⟩ => ?_
  have fm₈ : Frame [⟨s.gpr .r8, 8192⟩] s.mem s₈.mem := by
    rw [m₈, m₇', k₆.2.1]; exact fm₅
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [gt]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rest₈ (.rbx, 0) (by decide)
    · exact rest₈ (.rbp, 8) (by decide)
    · rw [g₈ _ (by decide), g₇' _ (by decide) (by decide), k₆.1 _ (by decide), k₅.1 _ (by decide),
        g₄ _ (by decide), g₃, k₂.1 _ (by decide), h₁.rsp]
    · exact rest₈ (.r12, 16) (by decide)
    · exact rest₈ (.r13, 24) (by decide)
    · exact rest₈ (.r14, 32) (by decide)
    · exact rest₈ (.r15, 40) (by decide)
  · have ft : Frame [⟨s.gpr .r8, 8192⟩, ⟨s.gpr .rdi, 32⟩] s.mem t.mem := by
      rw [mt]
      have c : ∀ d, d + 8 ≤ 32 → (⟨s.gpr .rdi, 32⟩ : Region).Contains (off (s.gpr .rdi) d) (64 / 8) :=
        fun d hd => Offset.contains_base _ hd (by omega)
      have hm : (⟨s.gpr .rdi, 32⟩ : Region) ∈ [⟨s.gpr .r8, 8192⟩, ⟨s.gpr .rdi, 32⟩] := by simp
      exact ((((fm₈.mono (by simp)).writeW hm _ (c 0 (by decide))).writeW hm _
        (c 8 (by decide))).writeW hm _ (c 16 (by decide))).writeW hm _ (c 24 (by decide))
    exact ft.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hs.ret_sc
      · exact hs.ret_out) (by decide)
  · change bytesAt t.mem (s.gpr .rdi) 32 = Spec.Ed25519.scalarMulAdd _ _ _
    rw [mt]
    change Spec.X25519.bytesAt (st4 _ _ _ _ _ _ _) _ 32 = _
    rw [bytesAt_st4, Spec.Ed25519.scalarMulAdd, encodeLE_eq]
    apply congrArg (Proof.X25519.leBytes 32)
    have v₈ : scalarValue s₈ = scalarValue s₆ := by
      simp only [scalarValue, g₈ .r8 (by decide), g₈ .r9 (by decide), g₈ .r10 (by decide),
        g₈ .r11 (by decide), g₇' .r8 (by decide) (by decide), g₇' .r9 (by decide) (by decide),
        g₇' .r10 (by decide) (by decide), g₇' .r11 (by decide) (by decide)]
    change scalarValue s₈ = _
    rw [v₈, val₆]
    have hd (p : Addr) : decodeLE (bytesAt s.mem p 32) = fe s.mem p 0 := by
      have h := decodeLE_words s.mem p 0
      rw [show off p 0 = p from BitVec.add_zero p] at h
      exact h
    rw [hd, hd, hd]

end VG.Proof.Ed25519.X86_64
