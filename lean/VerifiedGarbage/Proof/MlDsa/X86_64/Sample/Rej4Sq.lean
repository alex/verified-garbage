import VerifiedGarbage.Proof.MlKem.X86_64.S4Squeeze
import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejNtt4

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly4_avx2`, squeezing

`vg_mldsa_rej_ntt_poly4_avx2` absorbs the seeds and squeezes three blocks of
each as `vg_mlkem_sample_ntt4_avx2` does (`Proof/MlKem/X86_64/S4*.lean`, whose
precondition, layout and invariants it shares), then three more to the same
buffers. `SqT σ t n` is `SqInv σ n` (`S4Squeeze.lean`) after `t` blocks
squeezed before: the states are permuted `t + n` times, and the buffers hold
bytes `168 t` to `168 (t + n)` of each seed's output. A squeeze writes only
below the saved registers (`sqT_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Rej4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Proof.MlKem.X86_64 (Keep ea_at)
open VG.Proof.MlKem.X86_64.S4
open VG.Spec.MlKem (seed4 poly4)
open VG.Spec.Sha3 (keccakF RC)
open VG.Proof.Sha3 (byteOf iterF iterF_succ iterF_keccakF)
open VG.Proof.MlKem (xofByte)
open VG.Proof.Sha3.X86_64.X4 (la Lanes4 byte_of_lanes4 permute4_ok)

/-- After `n` squeezes, `t` blocks after the absorption. -/
structure SqT (σ : State) (t n : Nat) (s : State) : Prop where
  env : Env σ s
  r14 : s.gpr .r14 = 1
  rc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (scr σ) (50 + r) k) 64 = RC r
  lanes : Lanes4 s.mem (scr σ) fun k => iterF (t + n) (A0 (B σ k))
  buf : ∀ k < 4, ∀ p < 168 * n, s.mem (at' σ (oBuf + 504 * k + p)) = xofByte (B σ k) (168 * t + p)

theorem sqT_of {σ s : State} (h : SqInv σ 0 s) : SqT σ 0 0 s :=
  ⟨h.env, h.r14, h.rc, h.lanes, fun _ _ p hp => absurd hp (by omega)⟩

/-- The low part of the scratch space, which the squeezes write. -/
abbrev lowR (σ : State) : Region := ⟨scr σ, oSave⟩

/-- The permutation, after `n` squeezes. -/
theorem permT_ok {σ : State} (hp : Pre σ) {t n : Nat} (hn : n < 3) {s : State} (h : SqT σ t n s)
    {rest : Prog isa} {Q : State → Prop} (kont : ∀ s', Env σ s' ∧ s'.gpr .r14 = 1 ∧
      (∀ r < 24, ∀ k < 4, s'.mem.readW (la (scr σ) (50 + r) k) 64 = RC r) ∧
      Lanes4 s'.mem (scr σ) (fun k => iterF (t + n + 1) (A0 (B σ k))) ∧
      (∀ k < 4, ∀ p < 168 * n, s'.mem (at' σ (oBuf + 504 * k + p)) = xofByte (B σ k) (168 * t + p)) ∧
      Frame [lowR σ] s.mem s'.mem → WP isa rest s' Q) :
    WP isa (.seq (.block permArgs) (.seq Impl.Sha3.X86_64.X4.permute4 rest)) s Q := by
  refine WP.seq (WP.mono (args_ok h.env) fun s₁ ⟨⟨hm, hdi, hsi, hdx, hcx⟩, k₁⟩ => ?_)
  have hrd : s₁.rd = σ.rd := k₁.2.1.trans h.env.rd
  have hwr : s₁.wr = σ.wr := k₁.2.2.trans h.env.wr
  refine WP.seq (WP.mono (permute4_ok (A := fun k => iterF (t + n) (A0 (B σ k)))
    (pre4 hp hrd hwr (by rw [hm]; exact h.rc)) hdi hsi hdx (by rw [hcx, at', at', Offset.add_add])
    (by rw [hm]; exact h.lanes)) fun s₂ ⟨hl, hf, hrd₂, hwr₂, _, hg⟩ => kont s₂ ?_)
  have hsub : ∀ r ∈ [(⟨scr σ, 800⟩ : Region), ⟨at' σ 800, 800⟩], Region.Sub r ⟨scr σ, oSave⟩ := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by simp only [oSave]; omega)
    · exact Offset.sub_base _ (by simp only [oSave]; omega)
  refine ⟨Env.low (h.env.keep hm k₁ (by decide)) hsub hf hrd₂ hwr₂ fun r hr => hg r
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [hg _ (by decide) (by decide), k₁.gpr (by decide), h.r14], fun r hr k hk => ?_, ?_, fun k hk p hp' => ?_,
    by rw [← hm]; exact hf.sub fun r hr => ⟨lowR σ, List.mem_singleton_self _, hsub r hr⟩⟩
  · rw [hf.readW (Region.contains_self _ _) (by
        simpa using ⟨Offset.disjoint_base (scr σ) (k := 800) (d := 32 * (50 + r) + 8 * k) (n := 8) (by omega) (by omega),
          Offset.disjoint (scr σ) (d := 32 * (50 + r) + 8 * k) (n := 8) (e := 800) (k := 800) (by omega) (by omega)
            (by omega)⟩) (by decide), hm]
    exact h.rc r hr k hk
  · intro i hi k hk
    rw [hl i hi k hk]
    rfl
  · rw [buf_frame (by simpa using ⟨Offset.disjoint_base (scr σ) (k := 800) (d := oBuf) (n := 2016)
        (by simp only [oBuf]; omega) (by simp only [oBuf]; omega), Offset.disjoint (scr σ) (d := oBuf) (n := 2016)
          (e := 800) (k := 800) (by simp only [oBuf]; omega) (by simp only [oBuf]; omega) (by omega)⟩) hf hk (by omega), hm]
    exact h.buf k hk p hp'

/-- During the copy of block `n`: the first `I` lanes of state `K` copied,
and all of the states before it. -/
structure EXT (σ : State) (m₀ : Mem) (t n K I : Nat) (s : State) : Prop where
  env : Env σ s
  r14 : s.gpr .r14 = 1
  rc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (scr σ) (50 + r) k) 64 = RC r
  lanes : Lanes4 s.mem (scr σ) (fun k => iterF (t + n + 1) (A0 (B σ k)))
  buf : ∀ k < 4, ∀ p < 504, (p < 168 * n ∨ (168 * n ≤ p ∧ p < 168 * n + 168 ∧ (k < K ∨ (k = K ∧ p < 168 * n + 8 * I)))) →
    s.mem (at' σ (oBuf + 504 * k + p)) = xofByte (B σ k) (168 * t + p)
  fr : Frame [lowR σ] m₀ s.mem

open VG.Proof.Sha3.X86_64 (wp_movm wp_store wp_nil) in
theorem extT_step {σ : State} (hp : Pre σ) {m₀ : Mem} {t n K I : Nat} (hn : n < 3) (hK : K < 4) (hI : I < 21)
    {s : State} (h : EXT σ m₀ t n K I s) :
    WP isa (.block [.mov .rax (.mem (at_ .rbx (32 * I + 8 * K))),
      .store (at_ .rbx (oBuf + 504 * K + 168 * n + 8 * I)) .rax]) s (EXT σ m₀ t n K (I + 1)) := by
  refine wp_movm (a := at' σ (32 * I + 8 * K)) (by rw [ea_at, h.env.rbx])
    (in_scr' hp h.env.rd h.env.wr (by omega)) fun s₁ u₁ => wp_store (a := at' σ (oBuf + 504 * K + 168 * n + 8 * I))
      (by rw [ea_at, u₁.other _ (by decide), h.env.rbx]) (by rw [u₁.wr]; exact in_scr hp h.env.wr (by simp only [oBuf]; omega))
      fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (at' σ (oBuf + 504 * K + 168 * n + 8 * I)) (s.mem.readW (at' σ (32 * I + 8 * K)) 64) := by
    rw [m₂, u₁.mem, u₁.gpr]
  have hsub : Region.Sub ⟨at' σ (oBuf + 504 * K + 168 * n + 8 * I), 8⟩ (lowR σ) :=
    Offset.sub_base _ (by simp only [oBuf, oSave]; omega)
  have hf : Frame [⟨at' σ (oBuf + 504 * K + 168 * n + 8 * I), 8⟩] s.mem s₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨Env.low h.env (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsub) hf
      (r₂.trans u₁.rd) (w₂.trans u₁.wr)
      fun r hr => by
        rw [g₂, u₁.other r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)],
    by rw [g₂, u₁.other _ (by decide), h.r14], fun r hr k hk => ?_, fun i hi k hk => ?_, fun k hk p hp' hc => ?_,
    h.fr.trans (hf.sub fun r hr => ⟨lowR σ, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact hsub⟩)⟩
  · have e := readW_writeW_off s.mem (scr σ) (s.mem.readW (at' σ (32 * I + 8 * K)) 64) (d := 32 * (50 + r) + 8 * k)
      (e := oBuf + 504 * K + 168 * n + 8 * I) (n := 8) (by omega) (by simp only [oBuf]; omega)
      (by simp only [oBuf]; omega)
    rw [hm]; exact e.trans (h.rc r hr k hk)
  · have e := readW_writeW_off s.mem (scr σ) (s.mem.readW (at' σ (32 * I + 8 * K)) 64) (d := 32 * i + 8 * k)
      (e := oBuf + 504 * K + 168 * n + 8 * I) (n := 8) (by omega) (by simp only [oBuf]; omega)
      (by simp only [oBuf]; omega)
    rw [hm]; exact e.trans (h.lanes i hi k hk)
  · rw [hm]
    by_cases hw : k = K ∧ 168 * n + 8 * I ≤ p ∧ p < 168 * n + 8 * I + 8
    · obtain ⟨rfl, h₁, h₂⟩ := hw
      rw [wb_in _ _ _ (by omega) (by simp only [oBuf]; omega) (by decide),
        show 8 * (oBuf + 504 * k + p - (oBuf + 504 * k + 168 * n + 8 * I)) = 8 * (p - 168 * n - 8 * I) by omega,
        byte_readW _ _ (by omega), at', Offset.add_add,
        show 32 * I + 8 * k + (p - 168 * n - 8 * I) = 32 * ((8 * I + (p - 168 * n - 8 * I)) / 8) + 8 * k +
          (8 * I + (p - 168 * n - 8 * I)) % 8 by omega,
        byte_of_lanes4 h.lanes hk (by omega), show t + n + 1 = (t + n) + 1 from rfl,
        ← xofByte_A0 (B_length σ k) (by omega),
        show 168 * (t + n) + (8 * I + (p - 168 * n - 8 * I)) = 168 * t + p by omega]
    · rw [wb_out _ _ _ (by simp only [oBuf]; omega) (by simp only [oBuf]; omega) (by simp only [oBuf]; omega)]
      exact h.buf k hk p hp' (by omega)

/-- Block `n` of each state's output. -/
theorem extractT_ok {σ : State} (hp : Pre σ) {m₀ : Mem} {t n : Nat} (hn : n < 3) {s : State}
    (h : EXT σ m₀ t n 0 0 s) :
    WP isa (.block (extract n)) s fun s' => SqT σ t (n + 1) s' ∧ Frame [lowR σ] m₀ s'.mem := by
  rw [extract_eq]
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s => EXT σ m₀ t n K 0 s) (fun K s hK h => ?_) 4 (Nat.le_refl _)
    s h) fun s' h' => ⟨⟨h'.env, h'.r14, h'.rc, h'.lanes, fun k hk p hp' => h'.buf k hk p (by omega) (by omega)⟩, h'.fr⟩
  refine WP.mono (wp_range_flatMap (M := isa) (fun I s => EXT σ m₀ t n K I s) (fun I s hI h => extT_step hp hn hK hI h)
    21 (Nat.le_refl _) s h) fun s' h' =>
      ⟨h'.env, h'.r14, h'.rc, h'.lanes, fun k hk p hp' hc => h'.buf k hk p hp' (by omega), h'.fr⟩

/-- `squeeze4 n`: after `n + 1` squeezes; it writes only below the saved
registers. -/
theorem sqT_ok {σ : State} (hp : Pre σ) {t n : Nat} (hn : n < 3) {s : State} (h : SqT σ t n s) :
    WP isa (squeeze4 n) s fun s' => SqT σ t (n + 1) s' ∧ Frame [lowR σ] s.mem s'.mem := by
  unfold squeeze4
  exact permT_ok hp hn h fun s' ⟨he, h14, hrc, hl, hb, hf⟩ =>
    extractT_ok hp hn ⟨he, h14, hrc, hl, fun k hk p _ hc => hb k hk p (by omega), hf⟩

end VG.Proof.MlDsa.X86_64.Rej4
