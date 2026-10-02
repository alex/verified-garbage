import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# Scalar reduction: the complete function

The small target-specific contract below is implied by the merged signature
contract. It records the separation needed to preserve the input and return
address while saving registers, and the output's address while the loop keeps
it in the scratch.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Impl.X25519.X86_64 (at_ saved zero4)
open VG.Proof.X25519.X86_64
open VG.Spec.Ed25519 (bytesAt)

def scalarReduceLocal : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rsi, 64⟩] ∧ s.wr = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩] ∧
    (⟨s.gpr .rsi, 64⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 32⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (⟨s.gpr .rdi, 32⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩
  post s t := bytesAt t.mem (s.gpr .rdi) 32 =
    Spec.Ed25519.scalarReduce (bytesAt s.mem (s.gpr .rsi) 64)
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧
    s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx

theorem scalarSave_frame {base : Addr} {m m' : Mem} (h : Outside base 0 48 m m') :
    Frame [⟨base, 8192⟩] m m' := by
  intro x hx
  apply h x
  right
  have hn := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hn
  simp only [ofs]
  omega

theorem bytesAt_frame {m m' : Mem} {p base : Addr} (hf : Frame [⟨base, 8192⟩] m m')
    (hd : (⟨p, 64⟩ : Region).Disjoint ⟨base, 8192⟩) : bytesAt m' p 64 = bytesAt m p 64 := by
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, 64⟩) (by simpa only [List.mem_singleton, forall_eq])
    (by change 64 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)

theorem encodeLE_eq (n x : Nat) : Spec.Ed25519.encodeLE n x = Proof.X25519.leBytes n x := by
  simp only [Spec.Ed25519.encodeLE, Proof.X25519.leBytes, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem scalarReduce_correct {s : State} (hs : scalarReduceLocal.pre s) :
    WP isa scalarReduce s fun t => gprPreserved s t ∧ scalarReduceLocal.post s t := by
  obtain ⟨hr, hw, hd, hro, hrs, -⟩ := hs
  have hws : (⟨s.gpr .rdx, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  rw [scalarReduce]
  apply WP.seq
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (scalarSave_ok rfl hws) fun s₁ ⟨g₁, rd₁, wr₁, o₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (stashOut_ok (base := s.gpr .rdx) (by rw [g₁]) (by rw [wr₁]; exact hws))
    fun s₁' ⟨m₁', di₁', g₁', rd₁', wr₁'⟩ => ?_
  refine WP.mono (scalarInit_ok s₁') fun s₂ ⟨b₂, v₂, k₂⟩ => ?_
  have rsi₂ : s₂.gpr .rsi = s.gpr .rsi :=
    (k₂.1 _ (by decide)).trans ((g₁' _ (by decide)).trans (congrFun g₁ _))
  have rdi₂ : s₂.gpr .rdi = s.gpr .rdx := (k₂.1 _ (by decide)).trans di₁'
  have mem₂ : s₂.mem = s₁.mem.writeW (off (s.gpr .rdx) 48) (s.gpr .rdi) := by
    rw [k₂.2.1, m₁', g₁]
  have rw₂ : s₂.rd = s.rd ∧ s₂.wr = s.wr := ⟨by rw [k₂.2.2.1, rd₁', rd₁], by rw [k₂.2.2.2, wr₁', wr₁]⟩
  have read₂ : ∀ k < 8, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsi + BitVec.ofNat 64 (8 * k)) 8 := by
    intro k hk
    refine ⟨⟨s.gpr .rsi, 64⟩, ?_, ?_⟩
    · rw [rw₂.1, hr]; simp
    · rw [rsi₂]; exact Offset.contains_base _ (by omega) (by omega)
  have o₂ : Outside (s.gpr .rdx) 48 8 s₁.mem s₂.mem := by
    rw [mem₂]; exact writeW_outside _ _ _ (by omega)
  have fm₂ : Frame [⟨s.gpr .rdx, 8192⟩] s.mem s₂.mem :=
    (scalarSave_frame o₁).trans (scratchFrame o₂ (by decide))
  apply WP.seq
  refine WP.mono (scalarLoop_ok s₂ b₂ v₂ read₂) fun s₃ ⟨v₃, k₃⟩ => ?_
  have rdi₃ : s₃.gpr .rdi = s.gpr .rdx := (k₃.1 _ (by decide)).trans rdi₂
  have wr₃ : s₃.wr = s.wr := k₃.2.2.2.trans rw₂.2
  rw [WP.block_append_iff]
  refine WP.mono (finishArgs_ok rdi₃ (wr₃ ▸ hws)) fun s₄ ⟨dx₄, di₄, g₄', m₄', rd₄', wr₄'⟩ => ?_
  have sv₄ : Saved (s.gpr .rdx) s.gpr s₄.mem := by
    rw [m₄', k₃.2.1]; exact sv₁.outside o₂ (by decide)
  have out₄ : s₄.gpr .rdi = s.gpr .rdi := by
    rw [di₄, k₃.2.1, mem₂]; exact Mem.readW_writeW_self64 _ _ _
  rw [WP.block_append_iff]
  refine WP.mono (scalarRestore_ok dx₄ (by rw [wr₄', wr₃]; exact hws) sv₄)
    fun s₅ ⟨r₅, g₅, m₅, _, wr₅⟩ => ?_
  have rdi₅ : s₅.gpr .rdi = s.gpr .rdi := (g₅ _ (by decide)).trans out₄
  have hwo : (⟨s.gpr .rdi, 32⟩ : Region) ∈ s₅.wr := by rw [wr₅, wr₄', wr₃, hw]; simp
  refine WP.mono (scalarOut_ok rdi₅ hwo) fun t ⟨mt, gt, _, _⟩ => ?_
  have fm : Frame [⟨s.gpr .rdx, 8192⟩] s.mem s₅.mem := by
    rw [m₅, m₄', k₃.2.1]; exact fm₂
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [gt]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact r₅ (.rbx, 0) (by decide)
    · exact r₅ (.rbp, 8) (by decide)
    · rw [g₅ _ (by decide), g₄' _ (by decide) (by decide), k₃.1 _ (by decide), k₂.1 _ (by decide),
        g₁' _ (by decide), g₁]
    · exact r₅ (.r12, 16) (by decide)
    · exact r₅ (.r13, 24) (by decide)
    · exact r₅ (.r14, 32) (by decide)
    · exact r₅ (.r15, 40) (by decide)
  · have ft : Frame [⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rdi, 32⟩] s.mem t.mem := by
      rw [mt]
      have c : ∀ d, d + 8 ≤ 32 → (⟨s.gpr .rdi, 32⟩ : Region).Contains (off (s.gpr .rdi) d) (64 / 8) :=
        fun d hd => Offset.contains_base _ hd (by omega)
      have hm : (⟨s.gpr .rdi, 32⟩ : Region) ∈ [⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rdi, 32⟩] := by simp
      exact ((((fm.mono (by simp)).writeW hm _ (c 0 (by decide))).writeW hm _
        (c 8 (by decide))).writeW hm _ (c 16 (by decide))).writeW hm _ (c 24 (by decide))
    exact ft.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hrs
      · exact hro) (by decide)
  · change bytesAt t.mem (s.gpr .rdi) 32 = Spec.Ed25519.scalarReduce _
    rw [mt]
    change Spec.X25519.bytesAt (st4 _ _ _ _ _ _ _) _ 32 = _
    rw [bytesAt_st4, Spec.Ed25519.scalarReduce, encodeLE_eq]
    apply congrArg (Proof.X25519.leBytes 32)
    change scalarValue s₅ = _
    have val₅ : scalarValue s₅ = scalarValue s₃ := by
      simp only [scalarValue, g₅ .r8 (by decide), g₅ .r9 (by decide),
        g₅ .r10 (by decide), g₅ .r11 (by decide), g₄' .r8 (by decide) (by decide),
        g₄' .r9 (by decide) (by decide), g₄' .r10 (by decide) (by decide), g₄' .r11 (by decide) (by decide)]
    rw [val₅, v₃, rsi₂, bytesAt_frame fm₂ hd]

end VG.Proof.Ed25519.X86_64
