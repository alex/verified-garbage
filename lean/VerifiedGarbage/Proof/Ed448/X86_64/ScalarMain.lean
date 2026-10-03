import VerifiedGarbage.Proof.Ed448.X86_64.ScalarIO
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# Ed448 scalar reduction on x86-64: the whole function

The contract the proof is written against (the facts of
`Spec.Ed448.scalarReduceContract` it uses, stated for x86-64), and the
correctness of `vg_ed448_scalar_reduce` against it: every write is in the
working space but the result's, so the input is read unchanged, the
callee-saved registers are restored from the working space, and the return
address is kept.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Keeps Scr rv mv wv word off Outside ofs Saved saved_lt writeW_outside
  word_writeW_self contains_sc)
open VG.Impl.X448.X86_64 (W w sc at_ saved)
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-- `vg_ed448_scalar_reduce(out = rdi, wide = rsi, scratch = rdx)`. -/
def scalarReduceLocal : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rsi, 114⟩] ∧ s.wr = [⟨s.gpr .rdi, 57⟩, ⟨s.gpr .rdx, 8192⟩] ∧
    (⟨s.gpr .rsi, 114⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 57⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (⟨s.gpr .rdi, 57⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64
  post s t := bytesAt t.mem (s.gpr .rdi) 57 = Spec.Ed448.scalarReduce (bytesAt s.mem (s.gpr .rsi) 114)
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧
    s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx

/-- A byte of a region disjoint from the working space is beyond it. -/
theorem far {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < n) (hn : n ≤ 2 ^ 64) : 8192 ≤ ofs base (p + BitVec.ofNat 64 i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n)
    (by omega) (by omega)) ?_
  simp only [Region.Contains]; simp only [ofs] at h; omega

theorem Outside.frame {base : Addr} {m m' : Mem} (h : Outside base 0 8192 m m') :
    Frame [⟨base, 8192⟩] m m' := fun x hx => h x (Or.inr (by
  have := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at this; show 0 + 8192 ≤ (x - base).toNat; omega))

/-- The output's address at `OUT` of the working space `[b]`, and `b` into `rdi`. -/
theorem stash_ok {s : State} {base : Addr} (b : Reg) (hb : s.gpr b = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block [.store (at_ b OUT) .rdi, .mov .rdi (.reg b)]) s fun t =>
      t.mem = s.mem.writeW (off base OUT) (s.gpr .rdi) ∧ t.gpr .rdi = base ∧
      (∀ r, r ≠ .rdi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have w : InRegions s.wr (off base OUT) 8 := ⟨_, hw, contains_sc (by decide)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, ea_at, hb, State.store64, w,
    ite_true, RegUpd.gpr_setReg_self, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, trivial, fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr], rfl, rfl⟩

theorem scalarReduce_correct {s : State} (hp : scalarReduceLocal.pre s) :
    WP isa scalarReduce s fun t => gprPreserved s t ∧ scalarReduceLocal.post s t := by
  obtain ⟨hr, hw, hd, hro, hrs, hos, hn⟩ := hp
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .rdx = b := ⟨_, rfl⟩
  rw [hbase] at hd hrs hos hn
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hbase]; simp
  have hwo : (⟨s.gpr .rdi, 57⟩ : Region) ∈ s.wr := by rw [hw]; simp
  rw [scalarReduce]
  apply WP.seq
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (saveAt_ok .rdx hbase hws) fun s₁ ⟨g₁, rd₁, wr₁, o₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (stash_ok (base := base) .rdx (by rw [g₁]; exact hbase)
    (by rw [wr₁]; exact hws)) fun s₂ ⟨m₂, di₂, g₂, rd₂, wr₂⟩ => ?_
  have hs₂ : Scr s₂ base := ⟨di₂, by rw [wr₂, wr₁]; exact hws, by omega⟩
  refine WP.mono (storeK_ok hs₂) fun s₃ ⟨k₃, o₃, g₃, rd₃, wr₃⟩ => ?_
  have hs₃ : Scr s₃ base := ⟨(g₃ _ (by decide)).trans di₂, wr₃ ▸ hs₂.wr, hs₂.nowrap⟩
  have rsi₃ : s₃.gpr .rsi = s.gpr .rsi := by
    rw [g₃ _ (by decide), g₂ _ (by decide), g₁]
  have rw₃ : s₃.rd = s.rd ∧ s₃.wr = s.wr := ⟨by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩
  have o₂ : Outside base OUT 8 s₁.mem s₂.mem := by rw [m₂]; exact writeW_outside _ _ _ (by decide)
  -- The input, readable and outside the working space.
  have hin : ∀ i < 114, InRegions (s₃.rd ++ s₃.wr) (s.gpr .rsi + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨⟨s.gpr .rsi, 114⟩, by rw [rw₃.1, hr]; simp,
      Offset.contains_base _ (d := i) (n := 1) (k := 114) (by omega) (by omega)⟩
  have hfar : ∀ i < 114, 8192 ≤ ofs base (s.gpr .rsi + BitVec.ofNat 64 i) :=
    fun i hi => far hd hi (by decide)
  have O₃ : Outside base 0 8192 s.mem s₃.mem :=
    (o₁.mono (by decide) (by decide)).trans ((o₂.mono (by decide) (by decide)).trans
      (o₃.mono (by decide) (by decide)))
  have hmem₃ : bytesAt s₃.mem (s.gpr .rsi) 114 = bytesAt s.mem (s.gpr .rsi) 114 := by
    simp only [bytesAt]
    exact List.map_congr_left fun i hi => O₃ _ (Or.inr (hfar i (List.mem_range.mp hi)))
  apply WP.seq
  rw [reduce114]
  apply WP.seq
  refine WP.mono (init114_ok s₃ (by rw [rsi₃]; exact hin 112 (by decide))
    (by rw [rsi₃]; exact hin 113 (by decide))) fun s₄ ⟨v₄, b₄, k₄⟩ => ?_
  have hs₄ : Scr s₄ base := hs₃.of_keeps k₄ (by decide)
  have rsi₄ : s₄.gpr .rsi = s.gpr .rsi := (k₄.1 _ (by decide)).trans rsi₃
  have hK₄ : mv s₄.mem base KC 7 = wv kWords := by rw [k₄.2.1]; exact k₃
  have v₄' : rem s₄ = decodeLE (bytesAt s₄.mem (s₄.gpr .rsi + BitVec.ofNat 64 (8 * 14))
      (114 - 8 * 14)) % L := by
    rw [v₄, k₄.2.1, rsi₄, rsi₃]
    refine (Nat.mod_eq_of_lt ?_).symm
    rw [decode_two]
    have := (s₃.mem (s.gpr .rsi + BitVec.ofNat 64 112)).isLt
    have := (s₃.mem (s.gpr .rsi + BitVec.ofNat 64 112 + 1)).isLt
    have : 65536 < L := by decide +kernel
    omega
  refine WP.mono (scalarLoop_ok hs₄ hK₄ (len := 114) (n₀ := 14) (by decide) (by decide)
    ⟨by decide, b₄, v₄', fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩
    (fun k hk => by
      rw [rsi₄, k₄.2.2.1, k₄.2.2.2]
      exact ⟨⟨s.gpr .rsi, 114⟩, by rw [rw₃.1, hr]; simp,
        Offset.contains_base _ (d := 8 * k) (n := 8) (k := 114) (by omega) (by omega)⟩)
    (fun i hi => Or.inr (by rw [rsi₄]; have := hfar i hi; simp only [TMP]; omega)))
    fun s₅ ⟨v₅, g₅, rd₅, wr₅, o₅⟩ => ?_
  have hs₅ : Scr s₅ base := ⟨(g₅ _ (by decide)).trans hs₄.rdi, wr₅ ▸ hs₄.wr, hs₄.nowrap⟩
  have hout₅ : word s₅.mem base OUT = s.gpr .rdi := by
    rw [o₅.word (by decide) (by decide), k₄.2.1, o₃.word (by decide) (by decide), m₂,
      word_writeW_self, g₁]
  have sv₅ : Saved base s.gpr s₅.mem := by
    have sv₃ := (sv₁.outside o₂ (by decide)).outside o₃ (by decide)
    have sv₄ : Saved base s.gpr s₄.mem := by rw [k₄.2.1]; exact sv₃
    exact sv₄.outside o₅ (by decide)
  have hlt₅ : rem s₅ < L := by rw [v₅]; exact Nat.mod_lt _ L_pos
  refine WP.mono (finish_ok hs₅ hout₅ (by rw [wr₅, k₄.2.2.2, rw₃.2]; exact hwo) hos sv₅ hlt₅)
    fun t ⟨bt, rt, gt, ft, _, _⟩ => ?_
  have O₅ : Outside base 0 8192 s.mem s₅.mem := by
    have O₄ : Outside base 0 8192 s.mem s₄.mem := by rw [k₄.2.1]; exact O₃
    exact O₄.trans (o₅.mono (by decide) (by decide))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rt (.rbx, 0) (by decide)
    · exact rt (.rbp, 8) (by decide)
    · rw [gt _ (by decide), g₅ _ (by decide), k₄.1 _ (by decide), g₃ _ (by decide),
        g₂ _ (by decide), g₁]
    · exact rt (.r12, 16) (by decide)
    · exact rt (.r13, 24) (by decide)
    · exact rt (.r14, 32) (by decide)
    · exact rt (.r15, 40) (by decide)
  · have F : Frame [⟨base, 8192⟩, ⟨s.gpr .rdi, 57⟩] s.mem t.mem :=
      ((Outside.frame O₅).mono (by simp)).trans (ft.mono (by simp))
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hrs
      · exact hro) (by decide)
  · show bytesAt t.mem (s.gpr .rdi) 57 = _
    rw [bt, v₅, Spec.Ed448.scalarReduce, rsi₄, k₄.2.1, ← hmem₃]

end VG.Proof.Ed448.X86_64
