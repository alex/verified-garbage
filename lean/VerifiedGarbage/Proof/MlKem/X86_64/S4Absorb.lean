import VerifiedGarbage.Proof.MlKem.X86_64.S4Base

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, the round constants and the padded seeds

Untrusted: everything here is checked by Lean. After the prologue, the
table of the round constants (`rc_ok`), and the four states holding the
padded seeds, byte by byte (`absorb_ok`).
-/

namespace VG.Proof.MlKem.X86_64.S4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Spec.MlKem
open VG.Proof.Sha3.X86_64.X4 (q4 VUpd la ba Lanes4 wp_vmovq wp_vbcast wp_vst wp_vxor readW_write256 q4_ymm)
open VG.Proof.Sha3.X86_64 (wp_movi64)

/-- `Env` after writes below the saved registers. -/
theorem Env.write {σ s s' : State} (he : Env σ s) {a n : Nat} (h : a + n ≤ oSave)
    (hf : Frame [⟨at' σ a, n⟩] s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15], s'.gpr r = s.gpr r) : Env σ s' := by
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hg .rbx (by simp), he.rbx], by rw [hg .r12 (by simp), he.r12],
    by rw [hg .r13 (by simp), he.r13], by rw [hg .rsp (by simp), he.rsp], by rw [hg .r15 (by simp), he.r15],
    fun i hi => ?_, ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (by
        simpa using Offset.disjoint (scr σ) (d := oSave + 8 * i) (n := 8) (e := a) (k := n) (by simp only [oSave] at h ⊢; omega)
          (by simp only [oSave]; omega) (by simp only [oSave] at h; omega)) (by decide)]
    exact he.saved i hi
  · refine he.frame.trans (hf.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR σ, by simp, Offset.sub_base _ (by simp only [oSave] at h; omega)⟩

/-! ## Bytes written -/

/-- A byte of a write at `p + e`. -/
theorem wb_in (m : Mem) (p : Addr) {w : Nat} (v : BitVec w) {e d : Nat} (h₁ : e ≤ d) (h₂ : 8 * (d - e + 1) ≤ w)
    (hw : w < 2 ^ 64) : (m.writeW (p + BitVec.ofNat 64 e) v) (p + BitVec.ofNat 64 d) = v.extractLsb' (8 * (d - e)) 8 := by
  rw [← writeW_byte m _ v h₂ hw, Offset.add_add, Nat.add_sub_cancel' h₁]

/-- A byte outside a write at `p + e`. -/
theorem wb_out (m : Mem) (p : Addr) {w : Nat} (v : BitVec w) {e d : Nat} (h : d < e ∨ e + w / 8 ≤ d)
    (hd : d < 2 ^ 63) (he : e + w / 8 < 2 ^ 63) :
    (m.writeW (p + BitVec.ofNat 64 e) v) (p + BitVec.ofNat 64 d) = m (p + BitVec.ofNat 64 d) := by
  refine writeW_byte_off _ _ _ _ ?_
  rw [Offset.sub_toNat' _ (by omega) (by omega)]
  split <;> omega

/-! ## The round constants -/

/-- After the first `n` round constants. -/
structure RcInv (σ s₀ : State) (n : Nat) (s : State) : Prop where
  keep : Keep [.rax] s₀ s
  frame : Frame [⟨at' σ oRc, 768⟩] s₀.mem s.mem
  rc : ∀ r < n, ∀ k < 4, s.mem.readW (la (scr σ) (50 + r) k) 64 = Spec.Sha3.RC r

theorem rc_step {σ : State} (hp : Pre σ) {s₀ : State} (he : Env σ s₀) {r : Nat} (hr : r < 24) {s : State}
    (h : RcInv σ s₀ r s) :
    WP isa (.block [.movImm64 .rax (Spec.Sha3.RC r), .vop (.vmovq .xmm0 .rax),
      .vop (.vpbroadcastq .l256 .xmm0 .xmm0), Impl.Sha3.X86_64.X4.st .rbx (oRc / 32 + r) .xmm0]) s
      (RcInv σ s₀ (r + 1)) := by
  have hbx : s.gpr .rbx = scr σ := by rw [h.keep.gpr (by decide), he.rbx]
  refine wp_movi64 fun s₁ u₁ => wp_vmovq fun s₂ u₂ => wp_vbcast fun s₃ u₃ =>
    wp_vst (a := at' σ (32 * (50 + r))) (by rw [VG.Proof.Sha3.X86_64.ea_at, u₃.gpr, u₂.gpr, u₁.other _ (by decide), hbx]; rfl)
      (by rw [u₃.wr, u₂.wr, u₁.wr, h.keep.2.2, he.wr]; exact in_scr hp rfl (by omega))
      fun s₄ g₄ _ m₄ r₄ w₄ => VG.Proof.Sha3.X86_64.wp_nil ?_
  have hv : ∀ k < 4, q4 s₃ .xmm0 k = Spec.Sha3.RC r := fun k hk => by
    rw [u₃.val k hk, u₂.val 0 (by decide), ite_eq_left rfl, u₁.gpr]
  have hm : s₄.mem = s.mem.writeW (at' σ (32 * (50 + r))) (s₃.ymm .xmm0) := by rw [m₄, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨fun g hg => by rw [g₄, u₃.gpr, u₂.gpr, u₁.other g (by simpa using hg), h.keep.gpr hg],
      by rw [r₄, u₃.rd, u₂.rd, u₁.rd, h.keep.2.1], by rw [w₄, u₃.wr, u₂.wr, u₁.wr, h.keep.2.2]⟩, ?_,
    fun r' hr' k hk => ?_⟩
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by simp only [oRc]; omega)
      (by simp only [oRc]; omega) (by simp only [oRc]; omega))
  · rw [hm]
    by_cases e : r' = r
    · subst e
      rw [la, ← Offset.add_add, readW_write256 _ _ _ hk, q4_ymm _ _ hk, hv k hk]
    · have e := readW_writeW_off s.mem (scr σ) (s₃.ymm .xmm0) (d := 32 * (50 + r') + 8 * k)
        (e := 32 * (50 + r)) (n := 8) (by omega) (by omega) (by omega)
      exact e.trans (h.rc r' (by omega) k hk)

theorem rcTable_eq : Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) = (List.range 24).flatMap fun r =>
    [.movImm64 .rax (Spec.Sha3.RC r), .vop (.vmovq .xmm0 .rax), .vop (.vpbroadcastq .l256 .xmm0 .xmm0),
      Impl.Sha3.X86_64.X4.st .rbx (oRc / 32 + r) .xmm0] := rfl

/-- The table of the round constants. -/
theorem rc_ok {σ : State} (hp : Pre σ) {s₀ : State} (he : Env σ s₀) :
    WP isa (.block (Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32))) s₀ (RcInv σ s₀ 24) := by
  rw [rcTable_eq]
  exact wp_range_flatMap (M := isa) (RcInv σ s₀) (fun r s hr h => rc_step hp he hr h) 24 (Nat.le_refl _) s₀
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (by omega)⟩


/-! ## The states, byte by byte -/

/-- The offset of byte `q` of state `k`. -/
abbrev off4 (k q : Nat) : Nat := 32 * (q / 8) + 8 * k + q % 8

/-- The bytes of the states after a write at `p + e`. -/
theorem bytes_write {m : Mem} {p : Addr} {F : Nat → Nat → Byte}
    (h : ∀ k < 4, ∀ q < 200, m (ba p k q) = F k q) {w : Nat} (v : BitVec w) {e : Nat} (hw : w < 2 ^ 64)
    (he : e + w / 8 < 2 ^ 62) {k q : Nat} (hk : k < 4) (hq : q < 200) :
    (m.writeW (p + BitVec.ofNat 64 e) v) (ba p k q) =
      if e ≤ off4 k q ∧ off4 k q < e + w / 8 then v.extractLsb' (8 * (off4 k q - e)) 8 else F k q := by
  split
  · rename_i hc
    simp only [off4] at hc
    exact wb_in m p v hc.1 (by omega) hw
  · rename_i hc
    simp only [off4] at hc
    rw [ba, wb_out m p v (by omega) (by omega) (by omega)]
    exact h k hk q hq

/-- The four states hold `F`. -/
def SB (σ : State) (m : Mem) (F : Nat → Nat → Byte) : Prop :=
  ∀ k < 4, ∀ q < 200, m (ba (scr σ) k q) = F k q

/-- During the writes to the states, after the round constants (in `m₁`). -/
structure AI (σ : State) (m₁ : Mem) (s : State) : Prop where
  env : Env σ s
  r14 : s.gpr .r14 = 1
  frame : Frame [⟨scr σ, 800⟩] m₁ s.mem

theorem AI.write {σ : State} {m₁ : Mem} {s s' : State} (h : AI σ m₁ s) {e n : Nat} (hn : e + n ≤ 800)
    (hm : ∃ v : BitVec (8 * n), s'.mem = s.mem.writeW (at' σ e) v) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r) : AI σ m₁ s' := by
  obtain ⟨v, hv⟩ := hm
  have hf : Frame [⟨at' σ e, n⟩] s.mem s'.mem := by
    rw [hv]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
      rw [show 8 * n / 8 = n by omega]; exact Region.contains_self _ _)
  refine ⟨h.env.write (by simp only [oSave]; omega) hf hrd hwr fun r hr => hg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [hg _ (by decide), h.r14], h.frame.trans (hf.sub fun r hr => ?_)⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ hn⟩

/-! ### Zeroing -/

/-- After zeroing the first `n` lanes of each state. -/
structure ZInv (σ : State) (m₁ : Mem) (n : Nat) (s : State) : Prop where
  ai : AI σ m₁ s
  x0 : ∀ k < 4, q4 s .xmm0 k = 0
  bytes : ∀ k < 4, ∀ q < 200, q / 8 < n → s.mem (ba (scr σ) k q) = 0

theorem zero_step {σ : State} (hp : Pre σ) {m₁ : Mem} {i : Nat} (hi : i < 25) {s : State} (h : ZInv σ m₁ i s) :
    WP isa (.block [Impl.Sha3.X86_64.X4.st .rbx i .xmm0]) s (ZInv σ m₁ (i + 1)) := by
  refine wp_vst (a := at' σ (32 * i)) (by rw [VG.Proof.Sha3.X86_64.ea_at, h.ai.env.rbx])
    (by rw [h.ai.env.wr]; exact in_scr hp rfl (by omega)) fun s' g' q' m' r' w' => VG.Proof.Sha3.X86_64.wp_nil ?_
  refine ⟨h.ai.write (e := 32 * i) (n := 32) (by omega) ⟨_, m'⟩ r' w' fun r _ => by rw [g'],
    fun k hk => by rw [q', h.x0 k hk], fun k hk q hq hn => ?_⟩
  rw [m']
  have hb := bytes_write (m := s.mem) (p := scr σ) (F := fun k q => s.mem (ba (scr σ) k q))
    (fun _ _ _ _ => rfl) (s.ymm .xmm0) (e := 32 * i) (by decide) (by omega) hk hq
  rw [hb]
  split
  · rename_i hc
    simp only [off4] at hc ⊢
    rw [show 8 * (32 * (q / 8) + 8 * k + q % 8 - 32 * i) = 64 * k + 8 * (q % 8) by omega, ← extract_extract (s.ymm .xmm0) (64 * k) 64 (8 * (q % 8)) 8 (by omega),
      q4_ymm _ _ hk, h.x0 k hk]
    apply BitVec.eq_of_getLsbD_eq; intro j _; simp
  · rename_i hc
    simp only [off4] at hc
    exact h.bytes k hk q hq (by omega)

theorem zero4_eq : zero4 = Impl.Sha3.X86_64.X4.vb .vpxor .xmm0 .xmm0 .xmm0 ::
    (List.range 25).flatMap fun i => [Impl.Sha3.X86_64.X4.st .rbx i .xmm0] := rfl

theorem zero_ok {σ : State} (hp : Pre σ) {m₁ : Mem} {s : State} (h : AI σ m₁ s) :
    WP isa (.block zero4) s (fun s' => AI σ m₁ s' ∧ SB σ s'.mem fun _ _ => 0) := by
  rw [zero4_eq]
  refine wp_vxor fun s₁ u₁ => WP.mono (wp_range_flatMap (M := isa) (ZInv σ m₁) (fun i s hi h => zero_step hp hi h)
    25 (Nat.le_refl _) s₁ ⟨h.write (e := 0) (n := 0) (by omega) ⟨0, ?_⟩ u₁.rd u₁.wr fun r _ => by rw [u₁.gpr],
      fun k hk => by rw [u₁.val k hk, BitVec.xor_self]; rfl, fun _ _ _ _ h => absurd h (by omega)⟩)
    fun s' h' => ⟨h'.ai, fun k hk q hq => h'.bytes k hk q hq (by omega)⟩
  rw [u₁.mem]
  funext x
  simp [Mem.writeW, Mem.write]


/-! ### The seeds -/

/-- Byte `q` of seed `k` (0 past its end). -/
abbrev Bq (σ : State) (k q : Nat) : Byte := (B σ k).getD q 0

/-- The states after the first `K` seeds, and the first `i` lanes of seed `K`. -/
def HF (σ : State) (K i : Nat) (k q : Nat) : Byte :=
  if (k < K ∧ q < 34) ∨ (k = K ∧ q < 8 * i) then Bq σ k q else 0

open VG.Proof.Sha3.X86_64 (wp_movm wp_store wp_movzx8 wp_store8 wp_mov32i wp_nil) in
theorem lane_step {σ : State} (hp : Pre σ) {m₁ : Mem} {K i : Nat} (hK : K < 4) (hi : i < 4) {s : State}
    (h : AI σ m₁ s ∧ SB σ s.mem (HF σ K i)) :
    WP isa (.block [.mov .rax (.mem (at_ .r12 (34 * K + 8 * i))), .store (at_ .rbx (32 * i + 8 * K)) .rax]) s
      (fun s' => AI σ m₁ s' ∧ SB σ s'.mem (HF σ K (i + 1))) := by
  obtain ⟨ha, hb⟩ := h
  refine wp_movm (a := sd σ + BitVec.ofNat 64 (34 * K + 8 * i)) (by rw [ea_at, ha.env.r12])
    (in_sd' hp ha.env.rd ha.env.wr (by omega)) fun s₁ u₁ => wp_store (a := at' σ (32 * i + 8 * K))
      (by rw [ea_at, u₁.other _ (by decide), ha.env.rbx]) (by rw [u₁.wr]; exact in_scr hp ha.env.wr (by omega))
      fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (at' σ (32 * i + 8 * K)) (s.mem.readW (sd σ + BitVec.ofNat 64 (34 * K + 8 * i)) 64) := by
    rw [m₂, u₁.mem, u₁.gpr]
  refine ⟨ha.write (e := 32 * i + 8 * K) (n := 8) (by omega) ⟨_, hm⟩ (r₂.trans u₁.rd) (w₂.trans u₁.wr)
    fun r hr => by rw [g₂, u₁.other r hr], fun k hk q hq => ?_⟩
  rw [hm, bytes_write hb _ (by decide) (by omega) hk hq]
  simp only [off4]
  by_cases hc : 32 * i + 8 * K ≤ 32 * (q / 8) + 8 * k + q % 8 ∧ 32 * (q / 8) + 8 * k + q % 8 < 32 * i + 8 * K + 64 / 8
  · have hk' : k = K := by omega
    have hq' : q / 8 = i := by omega
    subst hk'
    rw [ifp hc, HF, ifp (.inr ⟨rfl, by omega⟩),
      show 8 * (32 * (q / 8) + 8 * k + q % 8 - (32 * i + 8 * k)) = 8 * (q % 8) by omega,
      byte_readW _ _ (by omega), Offset.add_add, show 34 * k + 8 * i + q % 8 = 34 * k + q by omega,
      seed_byte hp ha.env.frame hK (by omega)]
  · rw [ifn hc, HF, HF]
    by_cases hc' : (k < K ∧ q < 34) ∨ (k = K ∧ q < 8 * i)
    · rw [ifp hc', ifp (by omega)]
    · rw [ifn hc', ifn (by omega)]

theorem byte_setWidth (b : Byte) : BitVec.setWidth 8 (BitVec.setWidth 64 b) = b := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [hj]

open VG.Proof.Sha3.X86_64 (wp_movm wp_store wp_movzx8 wp_store8 wp_mov32i wp_nil) in
/-- Byte `32 + j` of seed `K`. -/
theorem byte_step {σ : State} (hp : Pre σ) {m₁ : Mem} {K j : Nat} (hK : K < 4) (hj : j < 2) {s : State}
    (h : AI σ m₁ s ∧ SB σ s.mem fun k q => if (k < K ∧ q < 34) ∨ (k = K ∧ q < 32 + j) then Bq σ k q else 0) :
    WP isa (.block [.movzx8 .rax (at_ .r12 (34 * K + (32 + j))), .store8 (at_ .rbx (128 + 8 * K + j)) .rax]) s
      (fun s' => AI σ m₁ s' ∧
        SB σ s'.mem fun k q => if (k < K ∧ q < 34) ∨ (k = K ∧ q < 32 + (j + 1)) then Bq σ k q else 0) := by
  obtain ⟨ha, hb⟩ := h
  refine wp_movzx8 (a := sd σ + BitVec.ofNat 64 (34 * K + (32 + j))) (by rw [ea_at, ha.env.r12])
    (in_sd' hp ha.env.rd ha.env.wr (by omega)) fun s₁ u₁ => wp_store8 (a := at' σ (128 + 8 * K + j))
      (by rw [ea_at, u₁.other _ (by decide), ha.env.rbx]) (by rw [u₁.wr]; exact in_scr hp ha.env.wr (by omega))
      fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (at' σ (128 + 8 * K + j)) (s.mem (sd σ + BitVec.ofNat 64 (34 * K + (32 + j)))) := by
    rw [m₂, u₁.mem, u₁.gpr, byte_setWidth]
  refine ⟨ha.write (e := 128 + 8 * K + j) (n := 1) (by omega) ⟨_, hm⟩ (r₂.trans u₁.rd) (w₂.trans u₁.wr)
    fun r hr => by rw [g₂, u₁.other r hr], fun k hk q hq => ?_⟩
  rw [hm, bytes_write hb _ (by decide) (by omega) hk hq]
  simp only [off4]
  by_cases hc : 128 + 8 * K + j ≤ 32 * (q / 8) + 8 * k + q % 8 ∧ 32 * (q / 8) + 8 * k + q % 8 < 128 + 8 * K + j + 8 / 8
  · have hk' : k = K := by omega
    have hq' : q = 32 + j := by omega
    subst hk' hq'
    rw [ifp hc, ifp (.inr ⟨rfl, by omega⟩), show 8 * (32 * ((32 + j) / 8) + 8 * k + (32 + j) % 8 -
      (128 + 8 * k + j)) = 0 by omega, Proof.Sha3.extractLsb'_byte, seed_byte hp ha.env.frame hK (by omega)]
  · rw [ifn hc]
    by_cases hc' : (k < K ∧ q < 34) ∨ (k = K ∧ q < 32 + j)
    · rw [ifp hc', ifp (by omega)]
    · rw [ifn hc', ifn (by omega)]

theorem seedLanes_eq (K : Nat) : seedLanes K = (List.range 4).flatMap (fun i =>
    [.mov .rax (.mem (at_ .r12 (34 * K + 8 * i))), .store (at_ .rbx (32 * i + 8 * K)) .rax]) ++
    (([.movzx8 .rax (at_ .r12 (34 * K + (32 + 0))), .store8 (at_ .rbx (128 + 8 * K + 0)) .rax] : List Instr) ++
      ([.movzx8 .rax (at_ .r12 (34 * K + (32 + 1))), .store8 (at_ .rbx (128 + 8 * K + 1)) .rax] : List Instr)) := by
  simp only [seedLanes, Nat.add_zero]; rfl

/-- The states after the first `K` seeds. -/
def GF (σ : State) (K : Nat) (k q : Nat) : Byte := if k < K ∧ q < 34 then Bq σ k q else 0

theorem seed_step {σ : State} (hp : Pre σ) {m₁ : Mem} {K : Nat} (hK : K < 4) {s : State}
    (h : AI σ m₁ s ∧ SB σ s.mem (GF σ K)) :
    WP isa (.block (seedLanes K)) s (fun s' => AI σ m₁ s' ∧ SB σ s'.mem (GF σ (K + 1))) := by
  rw [seedLanes_eq, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (fun i s => AI σ m₁ s ∧ SB σ s.mem (HF σ K i))
    (fun i s hi h => lane_step hp hK hi h) 4 (Nat.le_refl _) s ⟨h.1, fun k hk q hq => ?_⟩) fun s₁ h₁ => ?_
  · rw [h.2 k hk q hq, GF, HF]
    by_cases hc : k < K ∧ q < 34
    · rw [ifp hc, ifp (.inl hc)]
    · rw [ifn hc, ifn (by omega)]
  rw [WP.block_append_iff]
  refine WP.mono (byte_step hp (j := 0) hK (by decide) ⟨h₁.1, fun k hk q hq => ?_⟩) fun s₂ h₂ =>
    WP.mono (byte_step hp (j := 1) hK (by decide) h₂) fun s₃ ⟨h₃, b₃⟩ => ⟨h₃, fun k hk q hq => ?_⟩
  · rw [h₁.2 k hk q hq, HF]
  · rw [b₃ k hk q hq, GF]
    dsimp only
    by_cases hc : (k < K ∧ q < 34) ∨ (k = K ∧ q < 32 + (1 + 1))
    · rw [ifp hc]
      by_cases hc' : k < K + 1 ∧ q < 34
      · rw [ifp hc']
      · rw [ifn hc']; omega
    · rw [ifn hc]
      by_cases hc' : k < K + 1 ∧ q < 34
      · omega
      · rw [ifn hc']


/-! ### The padding -/

open VG.Proof.Sha3.X86_64 (wp_store8 wp_mov32i wp_nil) in
/-- The byte `c` (in `rax`) to byte `q₀` of state `K`. -/
theorem cbyte_step {σ : State} (hp : Pre σ) {m₁ : Mem} {F : Nat → Nat → Byte} {K q₀ : Nat} (hK : K < 4)
    (hq₀ : q₀ < 200) {c : Byte} {s : State} (hax : s.gpr .rax = c.setWidth 64) (h : AI σ m₁ s ∧ SB σ s.mem F) :
    WP isa (.block [.store8 (at_ .rbx (32 * (q₀ / 8) + 8 * K + q₀ % 8)) .rax]) s
      (fun s' => AI σ m₁ s' ∧ s'.gpr .rax = s.gpr .rax ∧
        SB σ s'.mem fun k q => if k = K ∧ q = q₀ then c else F k q) := by
  obtain ⟨ha, hb⟩ := h
  refine wp_store8 (a := at' σ (32 * (q₀ / 8) + 8 * K + q₀ % 8)) (by rw [ea_at, ha.env.rbx])
    (by exact in_scr hp ha.env.wr (by omega)) fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (at' σ (32 * (q₀ / 8) + 8 * K + q₀ % 8)) c := by
    rw [m₂, hax, byte_setWidth]
  refine ⟨ha.write (n := 1) (by omega) ⟨_, hm⟩ r₂ w₂ fun r _ => by rw [g₂], by rw [g₂], fun k hk q hq => ?_⟩
  rw [hm, bytes_write hb _ (by decide) (by omega) hk hq]
  simp only [off4]
  by_cases hc : 32 * (q₀ / 8) + 8 * K + q₀ % 8 ≤ 32 * (q / 8) + 8 * k + q % 8 ∧
      32 * (q / 8) + 8 * k + q % 8 < 32 * (q₀ / 8) + 8 * K + q₀ % 8 + 8 / 8
  · have e : k = K ∧ q = q₀ := by omega
    rw [ifp hc, ifp e, show 8 * (32 * (q / 8) + 8 * k + q % 8 - (32 * (q₀ / 8) + 8 * K + q₀ % 8)) = 0 by omega,
      Proof.Sha3.extractLsb'_byte]
  · rw [ifn hc, ifn (by omega)]

/-- The four states hold their padded seeds. -/
def PF (σ : State) (k q : Nat) : Byte :=
  if q < 34 then Bq σ k q else if q = 34 then 0x1f else if q = 167 then 0x80 else 0

theorem sfx_eq : (List.range 4).flatMap (fun k => [Instr.store8 (at_ .rbx (128 + 8 * k + 2)) .rax]) =
    (List.range 4).flatMap (fun k => [Instr.store8 (at_ .rbx (32 * (34 / 8) + 8 * k + 34 % 8)) .rax]) := rfl

theorem last_eq : (List.range 4).flatMap (fun k => [Instr.store8 (at_ .rbx (640 + 8 * k + 7)) .rax]) =
    (List.range 4).flatMap (fun k => [Instr.store8 (at_ .rbx (32 * (167 / 8) + 8 * k + 167 % 8)) .rax]) := rfl

/-- The byte `c` to byte `q₀` of each state. -/
theorem cbytes_ok {σ : State} (hp : Pre σ) {m₁ : Mem} {F : Nat → Nat → Byte} {q₀ : Nat} (hq₀ : q₀ < 200)
    {c : Byte} {s : State} (hax : s.gpr .rax = c.setWidth 64) (h : AI σ m₁ s ∧ SB σ s.mem F) :
    WP isa (.block ((List.range 4).flatMap fun k => [.store8 (at_ .rbx (32 * (q₀ / 8) + 8 * k + q₀ % 8)) .rax])) s
      (fun s' => AI σ m₁ s' ∧ SB σ s'.mem fun k q => if q = q₀ then c else F k q) := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s' => AI σ m₁ s' ∧ s'.gpr .rax = c.setWidth 64 ∧
      SB σ s'.mem fun k q => if k < K ∧ q = q₀ then c else F k q)
    (fun K s' hK ⟨ha, hx, hb⟩ => WP.mono (cbyte_step hp hK hq₀ hx ⟨ha, hb⟩) fun s'' ⟨ha', hx', hb'⟩ =>
      ⟨ha', hx'.trans hx, fun k hk q hq => ?_⟩) 4 (Nat.le_refl _) s ⟨h.1, hax, fun k hk q hq => ?_⟩)
    fun s' ⟨ha, _, hb⟩ => ⟨ha, fun k hk q hq => ?_⟩
  · rw [hb' k hk q hq]
    dsimp only
    by_cases e : k = K ∧ q = q₀
    · rw [ifp e, ifp (by omega)]
    · rw [ifn e]
      by_cases e' : k < K ∧ q = q₀
      · rw [ifp e', ifp (by omega)]
      · rw [ifn e', ifn (by omega)]
  · rw [h.2 k hk q hq]; dsimp only; rw [ifn (by omega)]
  · rw [hb k hk q hq]
    dsimp only
    by_cases e : q = q₀
    · rw [ifp e, ifp ⟨hk, e⟩]
    · rw [ifn e, ifn (by omega)]

theorem absorb4_eq : absorb4 = zero4 ++ ((List.range 4).flatMap seedLanes ++
    (([.mov32 .rax (.imm 0x1f)] : List Instr) ++ ((List.range 4).flatMap (fun k =>
      [Instr.store8 (at_ .rbx (32 * (34 / 8) + 8 * k + 34 % 8)) .rax]) ++
    (([.mov32 .rax (.imm 0x80)] : List Instr) ++ (List.range 4).flatMap (fun k =>
      [Instr.store8 (at_ .rbx (32 * (167 / 8) + 8 * k + 167 % 8)) .rax]))))) := by
  simp only [absorb4, List.append_assoc, List.cons_append, List.nil_append]

open VG.Proof.Sha3.X86_64 (wp_mov32i) in
/-- The padded seeds in the four states. -/
theorem absorb_ok {σ : State} (hp : Pre σ) {m₁ : Mem} {s : State} (h : AI σ m₁ s) :
    WP isa (.block absorb4) s (fun s' => AI σ m₁ s' ∧ SB σ s'.mem (PF σ)) := by
  rw [absorb4_eq, WP.block_append_iff]
  refine WP.mono (zero_ok hp h) fun s₁ ⟨h₁, z₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s => AI σ m₁ s ∧ SB σ s.mem (GF σ K))
    (fun K s hK h => seed_step hp hK h) 4 (Nat.le_refl _) s₁ ⟨h₁, fun k hk q hq => ?_⟩) fun s₂ h₂ => ?_
  · rw [z₁ k hk q hq, GF, ifn (by omega)]
  rw [WP.block_append_iff]
  refine WP.mono (wp_mov32i (is := []) fun s₃ u₃ => VG.Proof.Sha3.X86_64.wp_nil
    (Q := fun s₃ => AI σ m₁ s₃ ∧ s₃.gpr .rax = (0x1f : Byte).setWidth 64 ∧ SB σ s₃.mem (GF σ 4))
    ⟨h₂.1.write (e := 0) (n := 0) (by omega) ⟨0, ?_⟩ u₃.rd u₃.wr fun r hr => u₃.other r hr, by rw [u₃.gpr]; rfl,
      by rw [u₃.mem]; exact h₂.2⟩) fun s₃ ⟨a₃, x₃, b₃⟩ => ?_
  · rw [u₃.mem]; funext x; simp [Mem.writeW, Mem.write]
  rw [WP.block_append_iff]
  refine WP.mono (cbytes_ok hp (by decide) x₃ ⟨a₃, b₃⟩) fun s₄ ⟨a₄, b₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wp_mov32i (is := []) fun s₅ u₅ => VG.Proof.Sha3.X86_64.wp_nil
    (Q := fun s₅ => AI σ m₁ s₅ ∧ s₅.gpr .rax = (0x80 : Byte).setWidth 64 ∧
      SB σ s₅.mem fun k q => if q = 34 then 0x1f else GF σ 4 k q)
    ⟨a₄.write (e := 0) (n := 0) (by omega) ⟨0, ?_⟩ u₅.rd u₅.wr fun r hr => u₅.other r hr, by rw [u₅.gpr]; rfl,
      by rw [u₅.mem]; exact b₄⟩) fun s₅ ⟨a₅, x₅, b₅⟩ => ?_
  · rw [u₅.mem]; funext x; simp [Mem.writeW, Mem.write]
  refine WP.mono (cbytes_ok hp (by decide) x₅ ⟨a₅, b₅⟩) fun s₆ ⟨a₆, b₆⟩ => ⟨a₆, fun k hk q hq => ?_⟩
  rw [b₆ k hk q hq, PF]
  dsimp only
  rw [GF]
  by_cases e1 : q < 34
  · rw [ifn (show ¬ q = 167 by omega), ifn (show ¬ q = 34 by omega), ifp (show k < 4 ∧ q < 34 from ⟨hk, e1⟩),
      ifp e1]
  · rw [ifn e1, ifn (show ¬ (k < 4 ∧ q < 34) by omega)]
    by_cases e2 : q = 34
    · rw [ifn (show ¬ q = 167 by omega), ifp e2, ifp e2]
    · rw [ifn e2, ifn e2]

end VG.Proof.MlKem.X86_64.S4
