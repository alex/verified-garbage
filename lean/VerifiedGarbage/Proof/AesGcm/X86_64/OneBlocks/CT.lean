import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Facts
import VerifiedGarbage.Proof.AesGcm.X86_64.OneCT

/-!
# AES-GCM on x86-64: `oneBlocks` in two runs

Untrusted: everything here is checked by Lean. Both runs keep the same
length, branch the same way on it, and call `vg_aes_gcm_encrypt_blocks` or
`_decrypt_blocks` with the same arguments (`oneBlocks_rel`), so they leak
the same; after it, what stays in `W` is the data left and its length, and
the total length (`oneBlocks_oneS`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64

/-- The blocks of `oneBlocks`. -/
abbrev obB1 : List Instr :=
  [.mov .rax (.mem (at_ .r15 lenO)), .store (at_ .r15 tlenO) .rax, .shift .shr .rax 4, .alu .test .rax (.reg .rax)]
abbrev obB2 : List Instr :=
  ([.mov .rdi (.reg .r13), .mov .rsi (.mem (at_ .r15 roundsO))] : List Instr) ++ ptr .rdx .r14 48 ++
    ptr .rcx .r14 16 ++ ([.mov .r8 (.mem (at_ .r15 dataO)), .mov .r9 (.reg .rax)] : List Instr) ++ ptr .rax .r15 bScrO
abbrev obB3 : List Instr :=
  [.mov .rax (.mem (at_ .r15 lenO)), .mov .rcx (.reg .rax), .alu .and .rcx (imm 15), .store (at_ .r15 lenO) .rcx,
    .alu .sub .rax (.reg .rcx), .alu .add .rax (.mem (at_ .r15 dataO)), .store (at_ .r15 dataO) .rax]

theorem oneBlocks_eq (f : Fn) : oneBlocks f = .seq (.block obB1) (.ite .e (.block [])
    (.seq (.block obB2) (.seq (.frame (.push [.rax]) (.call f.name f.code) (.pop .rax 1)) (.block obB3)))) := rfl

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- The length kept, and the arguments of the call when there are whole blocks. -/
theorem ob12_ok {R : Nat} {D : Addr} {n : Nat} {s : State} (h : ObPre Ctx W SP R D n s) :
    WP isa (.block obB1) s fun s₁ => s₁.zf = some (decide (n / 16 = 0)) ∧
      Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧
      (n / 16 ≠ 0 → WP isa (.block obB2) s₁ (ObIn Ctx W SP R D n (n / 16))) := by
  have hn : n < 2 ^ 64 := h.data.ok.lt
  have he := h.env
  obtain ⟨e176, e200, -, -, -, -, -, -, -⟩ := w192_eqs L h (BitVec.ofNat 64 n)
  refine WP.mono (ob1_ok hn he h.len) fun s₁ ⟨r₁, z₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) rd₁ wr₁
  refine ⟨z₁, he₁, fun hz => ?_⟩
  have hR₁ : RoundsAt s₁.mem W R := ⟨by rw [m₁, e176]; exact h.rounds.1, h.rounds.2⟩
  have hd₁ : s₁.mem.readW (W + BitVec.ofNat 64 200) 64 = D := by rw [m₁, e200, h.dat]
  refine WP.mono (ob2_ok he₁ hR₁ hd₁) fun s₂ ⟨a1, a2, a3, a4, a5, a6, a7, g₂, m₂, rd₂, wr₂⟩ => ?_
  have he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) rd₂ wr₂
  exact ⟨he₂, h.data.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁), by omega, h.t_c, h.t_w, h.t_d, h.sp24, a1, a2, a3, a4,
    a5, by rw [a6, r₁], a7, h.rounds.2⟩

/-- `oneBlocks` of a function whose frame (`hf`, `hw`) leaks the same in two
runs with the same arguments. -/
theorem oneBlocks_rel (f : Fn) {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat}
    (t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩) (t_w : (below SP 24).Disjoint ⟨W, 2560⟩)
    (t_d : (below SP 24).Disjoint ⟨D, n⟩) (sp24 : 24 ≤ SP.toNat)
    (hf : RelCT isa (fun s₁ s₂ => ObIn Ctx W SP R D n (n / 16) s₁ ∧ ObIn Ctx W SP R D n (n / 16) s₂)
      (.frame (.push [.rax]) (.call f.name f.code) (.pop .rax 1)) fun _ _ => True)
    (hw : ∀ s, ObIn Ctx W SP R D n (n / 16) s →
      WP isa (.frame (.push [.rax]) (.call f.name f.code) (.pop .rax 1)) s
        fun s' => ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) :
    RelCT isa (OneS₂ Ctx W SP R A al D n T) (oneBlocks f) fun _ _ => True := by
  have pre : ∀ s, OneS Ctx W SP R A al D n T s → ObPre Ctx W SP R D n s := fun s h =>
    ⟨h.env, h.rounds, h.dat, h.len, h.dD, t_c, t_w, t_d, sp24⟩
  let G₁ : State → Prop := fun s₁ => s₁.zf = some (decide (n / 16 = 0)) ∧
    Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ (n / 16 ≠ 0 → WP isa (.block obB2) s₁ (ObIn Ctx W SP R D n (n / 16)))
  have a := rel_wp (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => OneS₂.env h) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) (G₁ := G₁) (G₂ := G₁) (fun s h => ob12_ok L (pre s h)) (fun s h => ob12_ok L (pre s h))
  have t := rel_taint (P := fun s₁ s₂ => (True ∧ G₁ s₁ ∧ G₁ s₂) ∧ s₁.zf = some true) (c := .block [])
    [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.2.1.2.1 h.1.2.2.2.1) ⟨_, by taint_decide⟩
  have hw₂ : ∀ s, G₁ s ∧ s.zf = some false → WP isa (.block obB2) s (ObIn Ctx W SP R D n (n / 16)) :=
    fun s h => h.1.2.2 fun hz => by have := h.1.1; rw [h.2] at this; simp [hz] at this
  have b := rel_wp (rel_taint (P := fun s₁ s₂ => (True ∧ G₁ s₁ ∧ G₁ s₂) ∧ s₁.zf = some false) (c := .block obB2)
      [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.2.1.2.1 h.1.2.2.2.1) ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨⟨h.1.2.1, h.2⟩, ⟨h.1.2.2, by rw [h.1.2.2.1, ← h.1.2.1.1, h.2]⟩⟩) hw₂ hw₂
  let G₃ : State → Prop := fun s => s.gpr .r13 = Ctx ∧ s.gpr .r14 = W + BitVec.ofNat 64 16 ∧ s.gpr .r15 = W ∧
    s.gpr .rsp = SP
  have hw₃ : ∀ s, ObIn Ctx W SP R D n (n / 16) s →
      WP isa (.frame (.push [.rax]) (.call f.name f.code) (.pop .rax 1)) s G₃ := fun s h =>
    WP.mono (hw s h) fun _ hc => ⟨by rw [hc .r13 (by decide)]; exact h.env.r13,
      by rw [hc .r14 (by decide)]; exact h.env.r14, by rw [hc .r15 (by decide)]; exact h.env.r15,
      by rw [hc .rsp (by decide)]; exact h.env.rsp⟩
  have c := rel_wp (hf.mono (P' := fun s₁ s₂ => True ∧ ObIn Ctx W SP R D n (n / 16) s₁ ∧
      ObIn Ctx W SP R D n (n / 16) s₂) (fun _ _ h => h.2) fun _ _ h => h) (fun _ _ h => h.2) hw₃ hw₃
  have d := rel_taint (P := fun s₁ s₂ => True ∧ G₃ s₁ ∧ G₃ s₂) (c := .block obB3) [.r13, .r14, .r15, .rsp]
    (fun _ _ h r hr => by
      obtain ⟨-, ⟨a₁, b₁, c₁, d₁⟩, ⟨a₂, b₂, c₂, d₂⟩⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [c₁, c₂]
      · rw [d₁, d₂]) ⟨_, by taint_decide⟩
  rw [oneBlocks_eq]
  exact RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.2.1.1, h.2.2.1]) t (RelCT.seq b (RelCT.seq c d)))

/-- After `oneBlocks`, what stays in `W`: the data left, its length and the
total length. -/
theorem oneBlocks_oneS (f : Fn) {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat}
    (t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩) (t_w : (below SP 24).Disjoint ⟨W, 2560⟩)
    (t_d : (below SP 24).Disjoint ⟨D, n⟩) (sp24 : 24 ≤ SP.toNat)
    (hw : ∀ s, ObIn Ctx W SP R D n (n / 16) s →
      WP isa (.frame (.push [.rax]) (.call f.name f.code) (.pop .rax 1)) s fun s' =>
        (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        Frame (obFrame W SP D (n / 16)) s.mem s'.mem)
    {s : State} (h : OneS Ctx W SP R A al D n T s) :
    WP isa (oneBlocks f) s (OneS Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n)) := by
  have hD := h.dD.ok.w
  refine WP.mono (oneBlocks_core L f (Out := fun _ _ => True) ⟨h.env, h.rounds, h.dat, h.len, h.dD, t_c, t_w, t_d, sp24⟩
    (fun s₂ hi => WP.mono (hw s₂ hi) fun _ ⟨a, b, c, d⟩ => ⟨a, b, c, d, trivial⟩) (fun _ _ _ => trivial)
    (fun _ _ _ _ _ _ => trivial)) fun s' ⟨P, _⟩ => ?_
  have fB := obFrame_B P.frame
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 192) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => fB.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrameB L hD t_w hd)
      (by decide)
  exact ⟨P.env, ⟨by rw [kp 176 (.inl ⟨by decide, by decide⟩)]; exact h.rounds.1, h.rounds.2⟩,
    by rw [kp 232 (.inr ⟨by decide, by decide⟩)]; exact h.aad, by rw [kp 184 (.inl ⟨by decide, by decide⟩)]; exact h.alen,
    P.dat, by rw [P.len]; congr 1; omega, h.dA.of_eq P.rd P.wr, (h.dD.of_eq P.rd P.wr).drop (by omega),
    fun N hN => by cases hN; exact P.tlen⟩

end

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

theorem obFrameE_rel {R : Nat} {D : Addr} {n q : Nat} :
    RelCT isa (fun s₁ s₂ => ObIn Ctx W SP R D n q s₁ ∧ ObIn Ctx W SP R D n q s₂)
      (.frame (.push [.rax]) (.call v.callees.enc.name v.callees.enc.code) (.pop .rax 1)) fun _ _ => True :=
  RelCT.frame (fun _ _ h => by rw [h.1.env.rsp, h.2.env.rsp]) (blkE_rel v fun _ _ ⟨s₁, s₂, hp, ha, hb⟩ =>
    ⟨_, _, _, _, _, _, _, ha ▸ ObIn.call L hp.1, hb ▸ ObIn.call L hp.2,
      by rw [ha, hb, pushed_rsp, pushed_rsp, hp.1.env.rsp, hp.2.env.rsp]⟩)

theorem obFrameD_rel {R : Nat} {D : Addr} {n q : Nat} :
    RelCT isa (fun s₁ s₂ => ObIn Ctx W SP R D n q s₁ ∧ ObIn Ctx W SP R D n q s₂)
      (.frame (.push [.rax]) (.call v.callees.dec.name v.callees.dec.code) (.pop .rax 1)) fun _ _ => True :=
  RelCT.frame (fun _ _ h => by rw [h.1.env.rsp, h.2.env.rsp]) (blkD_rel v fun _ _ ⟨s₁, s₂, hp, ha, hb⟩ =>
    ⟨_, _, _, _, _, _, _, ha ▸ ObIn.call L hp.1, hb ▸ ObIn.call L hp.2,
      by rw [ha, hb, pushed_rsp, pushed_rsp, hp.1.env.rsp, hp.2.env.rsp]⟩)

/-- `oneBlocks` encrypting, in two runs: after it, what stays in `W`. -/
theorem oneBlocksE_rel {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat}
    (t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩) (t_w : (below SP 24).Disjoint ⟨W, 2560⟩)
    (t_d : (below SP 24).Disjoint ⟨D, n⟩) (sp24 : 24 ≤ SP.toNat) :
    RelCT isa (OneS₂ Ctx W SP R A al D n T) (oneBlocks v.callees.enc)
      (OneS₂ Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n)) := by
  have hw := fun s => oneBlocks_oneS L v.callees.enc (R := R) (A := A) (al := al) (T := T) t_c t_w t_d sp24
    (fun s h => WP.mono (obFrameE_ok L v h) fun _ o => ⟨o.1, o.2.1, o.2.2.1, o.2.2.2.1⟩) (s := s)
  exact (rel_wp (oneBlocks_rel L v.callees.enc t_c t_w t_d sp24 (obFrameE_rel v L)
    (fun s h => WP.mono (obFrameE_ok L v h) fun _ o => o.1)) (fun _ _ h => h) hw hw).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-- `oneBlocks` decrypting, in two runs: after it, what stays in `W`. -/
theorem oneBlocksD_rel {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat}
    (t_c : (below SP 24).Disjoint ⟨Ctx, 256⟩) (t_w : (below SP 24).Disjoint ⟨W, 2560⟩)
    (t_d : (below SP 24).Disjoint ⟨D, n⟩) (sp24 : 24 ≤ SP.toNat) :
    RelCT isa (OneS₂ Ctx W SP R A al D n T) (oneBlocks v.callees.dec)
      (OneS₂ Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n)) := by
  have hw := fun s => oneBlocks_oneS L v.callees.dec (R := R) (A := A) (al := al) (T := T) t_c t_w t_d sp24
    (fun s h => WP.mono (obFrameD_ok L v h) fun _ o => ⟨o.1, o.2.1, o.2.2.1, o.2.2.2.1⟩) (s := s)
  exact (rel_wp (oneBlocks_rel L v.callees.dec t_c t_w t_d sp24 (obFrameD_rel v L)
    (fun s h => WP.mono (obFrameD_ok L v h) fun _ o => o.1)) (fun _ _ h => h) hw hw).mono
    (fun _ _ h => h) fun _ _ h => h.2

end

end VG.Proof.AesGcm.X86_64
