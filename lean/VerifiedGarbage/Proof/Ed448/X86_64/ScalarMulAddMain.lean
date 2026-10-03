import VerifiedGarbage.Proof.Ed448.X86_64.ScalarMulAdd

/-!
# Ed448 scalar multiply-add on x86-64: the whole function

The contract the proof is written against (the facts of
`Spec.Ed448.scalarMulAddContract` it uses, stated for x86-64), and the
correctness of `vg_ed448_scalar_mul_add` against it.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Keeps Scr rv mv wv word off Outside ofs Saved saved_lt writeW_outside
  word_writeW_self contains_sc stores_ok W_len)
open VG.Impl.X448.X86_64 (W w sc at_ saved loads stores chain)
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-- `vg_ed448_scalar_mul_add(out = rdi, r = rsi, k = rdx, s = rcx, scratch = r8)`. -/
def scalarMulAddLocal : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rsi, 57⟩, ⟨s.gpr .rdx, 57⟩, ⟨s.gpr .rcx, 57⟩] ∧
    s.wr = [⟨s.gpr .rdi, 57⟩, ⟨s.gpr .r8, 8192⟩] ∧
    (⟨s.gpr .rsi, 57⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩ ∧
    (⟨s.gpr .rdx, 57⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩ ∧
    (⟨s.gpr .rcx, 57⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 57⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩ ∧
    (⟨s.gpr .rdi, 57⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩ ∧
    (s.gpr .r8).toNat + 8192 ≤ 2 ^ 64
  post s t := bytesAt t.mem (s.gpr .rdi) 57 = Spec.Ed448.scalarMulAdd
    (bytesAt s.mem (s.gpr .rsi) 57) (bytesAt s.mem (s.gpr .rdx) 57) (bytesAt s.mem (s.gpr .rcx) 57)
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧
    s.gpr .rdx = t.gpr .rdx ∧ s.gpr .rcx = t.gpr .rcx ∧ s.gpr .r8 = t.gpr .r8

theorem mulAdd_mod (r k s : Nat) :
    ((k % L * (s % L)) % L + r % L) % L = (r + k * s) % L := by
  rw [← Nat.mul_mod, Nat.add_comm r, Nat.add_mod (k * s)]

theorem decode_acc (m : Mem) (base : Addr) :
    decodeLE (bytesAt m (base + BitVec.ofNat 64 Impl.X448.X86_64.ACC) 112) =
      mv m base Impl.X448.X86_64.ACC 14 := by
  rw [decodeLE_eq]
  exact Proof.X448.X86_64.leNum_bytesAt_mv m base Impl.X448.X86_64.ACC 14

/-- A stores into the slot `o` (seven words) of the working space. -/
theorem storeSlot_ok {s : State} {base : Addr} (hs : Scr s base) (o : Nat) (ho : o + 56 ≤ 8192) :
    WP isa (.block (stores o W)) s fun t => mv t.mem base o 7 = rem s ∧ Outside base o 56 s.mem t.mem ∧
      (∀ r, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  WP.mono (stores_ok hs o W (by rw [W_len]; omega)) fun t ⟨v, o', g, rd, wr⟩ =>
    ⟨by rw [W_len] at v; exact v, by rw [W_len] at o'; exact o', g, rd, wr⟩

theorem bytes_far {base p : Addr} {m m' : Mem} {n : Nat} (h : Outside base 0 8192 m m')
    (hp : ∀ i < n, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h _ (Or.inr (hp i (List.mem_range.mp hi)))

theorem scalarMulAdd_correct {s : State} (hp : scalarMulAddLocal.pre s) :
    WP isa scalarMulAdd s fun t => gprPreserved s t ∧ scalarMulAddLocal.post s t := by
  obtain ⟨hr, hw, hdr, hdk, hds, hro, hrs, hos, hn⟩ := hp
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .r8 = b := ⟨_, rfl⟩
  rw [hbase] at hdr hdk hds hrs hos hn
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hbase]; simp
  have hwo : (⟨s.gpr .rdi, 57⟩ : Region) ∈ s.wr := by rw [hw]; simp
  have farR : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rsi + BitVec.ofNat 64 i) :=
    fun i hi => far hdr hi (by decide)
  have farK : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rdx + BitVec.ofNat 64 i) :=
    fun i hi => far hdk hi (by decide)
  have farS : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rcx + BitVec.ofNat 64 i) :=
    fun i hi => far hds hi (by decide)
  rw [scalarMulAdd]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (saveAt_ok .r8 hbase hws) fun s₁ ⟨g₁, rd₁, wr₁, o₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (args_ok (base := base) (by rw [g₁]; exact hbase) (by rw [wr₁]; exact hws))
    fun s₂ ⟨aO₂, aR₂, aK₂, aS₂, o₂, di₂, g₂, rd₂, wr₂⟩ => ?_
  have hs₂ : Scr s₂ base := ⟨di₂, by rw [wr₂, wr₁]; exact hws, by omega⟩
  rw [WP.block_append_iff]
  refine WP.mono (storeK_ok hs₂) fun s₃ ⟨k₃, o₃, g₃, rd₃, wr₃⟩ => ?_
  have hs₃ : Scr s₃ base := ⟨(g₃ _ (by decide)).trans di₂, wr₃ ▸ hs₂.wr, hs₂.nowrap⟩
  refine WP.mono (loadRsi_ok hs₃ (d := ARG_K) (by decide)) fun s₄ ⟨rsi₄, k₄⟩ => ?_
  have hs₄ : Scr s₄ base := hs₃.of_keeps k₄ (by decide)
  have rd₄ : s₄.rd = s.rd := by rw [k₄.2.2.1, rd₃, rd₂, rd₁]
  have wr₄ : s₄.wr = s.wr := by rw [k₄.2.2.2, wr₃, wr₂, wr₁]
  have O₄ : Outside base 0 8192 s.mem s₄.mem := by
    rw [k₄.2.1]
    exact (o₁.mono (by decide) (by decide)).trans ((o₂.mono (by decide) (by decide)).trans
      (o₃.mono (by decide) (by decide)))
  have kp₄ : s₄.gpr .rsi = s.gpr .rdx := by
    rw [rsi₄, o₃.word (by decide) (by decide), aK₂, g₁]
  have hR₄ : (⟨s₄.gpr .rsi, 57⟩ : Region) ∈ s₄.rd ++ s₄.wr := by
    rw [kp₄, rd₄, hr]; simp
  -- k mod L
  apply WP.seq
  refine WP.mono (reduce57_ok hs₄ (by rw [k₄.2.1]; exact k₃) hR₄ (by rw [kp₄]; exact farK))
    fun s₅ ⟨v₅, g₅, rd₅, wr₅, o₅⟩ => ?_
  have hs₅ : Scr s₅ base := ⟨(g₅ _ (by decide)).trans hs₄.rdi, wr₅ ▸ hs₄.wr, hs₄.nowrap⟩
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (storeSlot_ok hs₅ SK (by decide)) fun s₆ ⟨m₆, o₆, g₆, rd₆, wr₆⟩ => ?_
  have hs₆ : Scr s₆ base := ⟨(g₆ _).trans hs₅.rdi, wr₆ ▸ hs₅.wr, hs₅.nowrap⟩
  refine WP.mono (loadRsi_ok hs₆ (d := ARG_S) (by decide)) fun s₇ ⟨rsi₇, k₇⟩ => ?_
  have hs₇ : Scr s₇ base := hs₆.of_keeps k₇ (by decide)
  have rd₇ : s₇.rd = s.rd := by rw [k₇.2.2.1, rd₆, rd₅, rd₄]
  have wr₇ : s₇.wr = s.wr := by rw [k₇.2.2.2, wr₆, wr₅, wr₄]
  have O₇ : Outside base 0 8192 s.mem s₇.mem := by
    rw [k₇.2.1]
    exact O₄.trans ((o₅.mono (by decide) (by decide)).trans (o₆.mono (by decide) (by decide)))
  have kp₇ : s₇.gpr .rsi = s.gpr .rcx := by
    rw [rsi₇, o₆.word (by decide) (by decide), o₅.word (by decide) (by decide), k₄.2.1,
      o₃.word (by decide) (by decide), aS₂, g₁]
  have hK₇ : mv s₇.mem base KC 7 = wv kWords := by
    rw [k₇.2.1, o₆.mv (by decide) (by decide), o₅.mv (by decide) (by decide), k₄.2.1, k₃]
  -- s mod L
  apply WP.seq
  refine WP.mono (reduce57_ok hs₇ hK₇ (by rw [kp₇, rd₇, hr]; simp) (by rw [kp₇]; exact farS))
    fun s₈ ⟨v₈, g₈, rd₈, wr₈, o₈⟩ => ?_
  have hs₈ : Scr s₈ base := ⟨(g₈ _ (by decide)).trans hs₇.rdi, wr₈ ▸ hs₇.wr, hs₇.nowrap⟩
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (storeSlot_ok hs₈ SS (by decide)) fun s₉ ⟨m₉, o₉, g₉, rd₉, wr₉⟩ => ?_
  have hs₉ : Scr s₉ base := ⟨(g₉ _).trans hs₈.rdi, wr₉ ▸ hs₈.wr, hs₈.nowrap⟩
  refine WP.mono (loadRsi_ok hs₉ (d := ARG_R) (by decide)) fun s₁₀ ⟨rsi₁₀, k₁₀⟩ => ?_
  have hs₁₀ : Scr s₁₀ base := hs₉.of_keeps k₁₀ (by decide)
  have rd₁₀ : s₁₀.rd = s.rd := by rw [k₁₀.2.2.1, rd₉, rd₈, rd₇]
  have wr₁₀ : s₁₀.wr = s.wr := by rw [k₁₀.2.2.2, wr₉, wr₈, wr₇]
  have O₁₀ : Outside base 0 8192 s.mem s₁₀.mem := by
    rw [k₁₀.2.1]
    exact O₇.trans ((o₈.mono (by decide) (by decide)).trans (o₉.mono (by decide) (by decide)))
  have kp₁₀ : s₁₀.gpr .rsi = s.gpr .rsi := by
    rw [rsi₁₀, o₉.word (by decide) (by decide), o₈.word (by decide) (by decide), k₇.2.1,
      o₆.word (by decide) (by decide), o₅.word (by decide) (by decide), k₄.2.1,
      o₃.word (by decide) (by decide), aR₂, g₁]
  have hK₁₀ : mv s₁₀.mem base KC 7 = wv kWords := by
    rw [k₁₀.2.1, o₉.mv (by decide) (by decide), o₈.mv (by decide) (by decide), hK₇]
  -- r mod L
  apply WP.seq
  refine WP.mono (reduce57_ok hs₁₀ hK₁₀ (by rw [kp₁₀, rd₁₀, hr]; simp) (by rw [kp₁₀]; exact farR))
    fun s₁₁ ⟨v₁₁, g₁₁, rd₁₁, wr₁₁, o₁₁⟩ => ?_
  have hs₁₁ : Scr s₁₁ base := ⟨(g₁₁ _ (by decide)).trans hs₁₀.rdi, wr₁₁ ▸ hs₁₀.wr, hs₁₀.nowrap⟩
  -- The product.
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (storeSlot_ok hs₁₁ SR (by decide)) fun s₁₂ ⟨m₁₂, o₁₂, g₁₂, rd₁₂, wr₁₂⟩ => ?_
  have hs₁₂ : Scr s₁₂ base := ⟨(g₁₂ _).trans hs₁₁.rdi, wr₁₂ ▸ hs₁₁.wr, hs₁₁.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (product_ok hs₁₂) fun s₁₃ ⟨e₁₃, g₁₃, rd₁₃, wr₁₃, o₁₃⟩ => ?_
  have hs₁₃ : Scr s₁₃ base := ⟨(g₁₃ _ (by decide)).trans hs₁₂.rdi, wr₁₃ ▸ hs₁₂.wr, hs₁₂.nowrap⟩
  refine WP.mono (accInit_ok hs₁₃) fun s₁₄ ⟨rsi₁₄, v₁₄, b₁₄, k₁₄⟩ => ?_
  have hs₁₄ : Scr s₁₄ base := hs₁₃.of_keeps k₁₄ (by decide)
  have hK₁₄ : mv s₁₄.mem base KC 7 = wv kWords := by
    rw [k₁₄.2.1, o₁₃.mv (by decide) (by decide), o₁₂.mv (by decide) (by decide),
      o₁₁.mv (by decide) (by decide), hK₁₀]
  -- The product's words, reduced.
  apply WP.seq
  refine WP.mono (scalarLoop_ok hs₁₄ hK₁₄ (len := 112) (n₀ := 14) (by decide) (by decide)
    ⟨by decide, b₁₄, by rw [v₁₄]; rfl, fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩
    (fun k hk => by
      rw [rsi₁₄, Offset.add_add]
      exact ⟨_, List.mem_append_right _ hs₁₄.wr, contains_sc (by simp only [Impl.X448.X86_64.ACC]; omega)⟩)
    (fun i hi => Or.inr (by
      rw [rsi₁₄, Proof.X448.X86_64.ofs_off base (by simp only [Impl.X448.X86_64.ACC]; omega)]
      simp only [Impl.X448.X86_64.ACC, TMP]; omega)))
    fun s₁₅ ⟨v₁₅, g₁₅, rd₁₅, wr₁₅, o₁₅⟩ => ?_
  have hs₁₅ : Scr s₁₅ base := ⟨(g₁₅ _ (by decide)).trans hs₁₄.rdi, wr₁₅ ▸ hs₁₄.wr, hs₁₄.nowrap⟩
  -- The three reduced inputs.
  have eK : mv s₁₂.mem base SK 7 = decodeLE (bytesAt s.mem (s.gpr .rdx) 57) % L := by
    rw [o₁₂.mv (by decide) (by decide), o₁₁.mv (by decide) (by decide), k₁₀.2.1,
      o₉.mv (by decide) (by decide), o₈.mv (by decide) (by decide), k₇.2.1, m₆, v₅, kp₄,
      bytes_far O₄ farK]
  have eS : mv s₁₂.mem base SS 7 = decodeLE (bytesAt s.mem (s.gpr .rcx) 57) % L := by
    rw [o₁₂.mv (by decide) (by decide), o₁₁.mv (by decide) (by decide), k₁₀.2.1, m₉, v₈, kp₇,
      bytes_far O₇ farS]
  have eR : mv s₁₅.mem base SR 7 = decodeLE (bytesAt s.mem (s.gpr .rsi) 57) % L := by
    rw [o₁₅.mv (by decide) (by decide), k₁₄.2.1, o₁₃.mv (by decide) (by decide), m₁₂, v₁₁, kp₁₀,
      bytes_far O₁₀ farR]
  have e₁₅ : rem s₁₅ = (decodeLE (bytesAt s.mem (s.gpr .rdx) 57) % L *
      (decodeLE (bytesAt s.mem (s.gpr .rcx) 57) % L)) % L := by
    rw [v₁₅, rsi₁₄, decode_acc, k₁₄.2.1, e₁₃, eK, eS]
  have hL := L_pos
  rw [WP.block_append_iff]
  refine WP.mono (addSR_ok hs₁₅ (by
    rw [e₁₅, eR]
    have := Nat.mod_lt (decodeLE (bytesAt s.mem (s.gpr .rsi) 57)) hL
    have := Nat.mod_lt (decodeLE (bytesAt s.mem (s.gpr .rdx) 57) % L *
      (decodeLE (bytesAt s.mem (s.gpr .rcx) 57) % L)) hL
    omega)) fun s₁₆ ⟨v₁₆, k₁₆⟩ => ?_
  have hs₁₆ : Scr s₁₆ base := hs₁₅.of_keeps k₁₆ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (csub_ok hs₁₆ (by
      rw [k₁₆.2.1, o₁₅.mv (by decide) (by decide)]; exact hK₁₄)
    (by
      rw [v₁₆, e₁₅, eR]
      have := Nat.mod_lt (decodeLE (bytesAt s.mem (s.gpr .rsi) 57)) hL
      have := Nat.mod_lt (decodeLE (bytesAt s.mem (s.gpr .rdx) 57) % L *
        (decodeLE (bytesAt s.mem (s.gpr .rcx) 57) % L)) hL
      omega)) fun s₁₇ ⟨v₁₇, g₁₇, rd₁₇, wr₁₇, o₁₇⟩ => ?_
  have hs₁₇ : Scr s₁₇ base := ⟨(g₁₇ _ (by decide)).trans hs₁₆.rdi, wr₁₇ ▸ hs₁₆.wr, hs₁₆.nowrap⟩
  have hout : word s₁₇.mem base OUT = s.gpr .rdi := by
    rw [o₁₇.word (by decide) (by decide), k₁₆.2.1, o₁₅.word (by decide) (by decide), k₁₄.2.1,
      o₁₃.word (by decide) (by decide), o₁₂.word (by decide) (by decide),
      o₁₁.word (by decide) (by decide), k₁₀.2.1, o₉.word (by decide) (by decide),
      o₈.word (by decide) (by decide), k₇.2.1, o₆.word (by decide) (by decide),
      o₅.word (by decide) (by decide), k₄.2.1, o₃.word (by decide) (by decide), aO₂, g₁]
  have sv : Saved base s.gpr s₁₇.mem := by
    have h₃ := (sv₁.outside o₂ (by decide)).outside o₃ (by decide)
    have h₄ : Saved base s.gpr s₄.mem := by rw [k₄.2.1]; exact h₃
    have h₆ := (h₄.outside o₅ (by decide)).outside o₆ (by decide)
    have h₇ : Saved base s.gpr s₇.mem := by rw [k₇.2.1]; exact h₆
    have h₉ := (h₇.outside o₈ (by decide)).outside o₉ (by decide)
    have h₁₀ : Saved base s.gpr s₁₀.mem := by rw [k₁₀.2.1]; exact h₉
    have h₁₃ := ((h₁₀.outside o₁₁ (by decide)).outside o₁₂ (by decide)).outside o₁₃ (by decide)
    have h₁₄ : Saved base s.gpr s₁₄.mem := by rw [k₁₄.2.1]; exact h₁₃
    have h₁₅ := h₁₄.outside o₁₅ (by decide)
    have h₁₆ : Saved base s.gpr s₁₆.mem := by rw [k₁₆.2.1]; exact h₁₅
    exact h₁₆.outside o₁₇ (by decide)
  have hlt : rem s₁₇ < L := by rw [v₁₇]; exact Nat.mod_lt _ hL
  have hwo₁₇ : (⟨s.gpr .rdi, 57⟩ : Region) ∈ s₁₇.wr := by
    rw [wr₁₇, k₁₆.2.2.2, wr₁₅, k₁₄.2.2.2, wr₁₃, wr₁₂, wr₁₁, wr₁₀]; exact hwo
  refine WP.mono (finish_ok hs₁₇ hout hwo₁₇ hos sv hlt) fun t ⟨bt, rt, gt, ft, _, _⟩ => ?_
  have O : Outside base 0 8192 s.mem s₁₇.mem := by
    have O₁₄ : Outside base 0 8192 s.mem s₁₄.mem := by
      rw [k₁₄.2.1]
      exact O₁₀.trans ((o₁₁.mono (by decide) (by decide)).trans ((o₁₂.mono (by decide)
        (by decide)).trans (o₁₃.mono (by decide) (by decide))))
    have O₁₆ : Outside base 0 8192 s.mem s₁₆.mem := by
      rw [k₁₆.2.1]; exact O₁₄.trans (o₁₅.mono (by decide) (by decide))
    exact O₁₆.trans (o₁₇.mono (by decide) (by decide))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rt (.rbx, 0) (by decide)
    · exact rt (.rbp, 8) (by decide)
    · rw [gt _ (by decide), g₁₇ _ (by decide), k₁₆.1 _ (by decide), g₁₅ _ (by decide),
        k₁₄.1 _ (by decide), g₁₃ _ (by decide), g₁₂, g₁₁ _ (by decide), k₁₀.1 _ (by decide), g₉,
        g₈ _ (by decide), k₇.1 _ (by decide), g₆, g₅ _ (by decide), k₄.1 _ (by decide),
        g₃ _ (by decide), g₂ _ (by decide), g₁]
    · exact rt (.r12, 16) (by decide)
    · exact rt (.r13, 24) (by decide)
    · exact rt (.r14, 32) (by decide)
    · exact rt (.r15, 40) (by decide)
  · have F : Frame [⟨base, 8192⟩, ⟨s.gpr .rdi, 57⟩] s.mem t.mem :=
      ((Outside.frame O).mono (by simp)).trans (ft.mono (by simp))
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hrs
      · exact hro) (by decide)
  · show bytesAt t.mem (s.gpr .rdi) 57 = _
    rw [bt, v₁₇, v₁₆, e₁₅, eR, Spec.Ed448.scalarMulAdd, mulAdd_mod]

end VG.Proof.Ed448.X86_64
