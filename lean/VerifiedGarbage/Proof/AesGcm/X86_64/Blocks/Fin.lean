import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Tail

/-!
# AES-GCM on whole blocks, x86-64: the end

Untrusted: everything here is checked by Lean. From `Mid s q q ys`, `tail`
calls `vg_aes_ctr32` and `vg_ghash` on the blocks left (if any), and
the counter mode and GHASH of the two parts make those of all the blocks
(`ctr32_append`, `ghashFrom_append`): `encTail_ok`, `decTail_ok`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- `scratch` on the stack is apart from the return addresses of calls. -/
theorem arg_below (SP : Addr) : (⟨SP + BitVec.ofNat 64 8, 8⟩ : Region).Disjoint (below SP 8) :=
  Offset.disjoint_below SP (n := 8) (d := 8) (k := 8) (by decide)

/-- A region apart from what a call of `vg_aes_ctr32` or `vg_ghash` on the
blocks left writes. -/
structure Apart (s : State) (q : Nat) (r : Region) : Prop where
  c : r.Disjoint (cR s)
  y : r.Disjoint (yR s)
  d : r.Disjoint ⟨dq s q, 16 * (n s - q)⟩
  s5 : r.Disjoint ⟨S5 s, 2048⟩
  t : r.Disjoint (below (SP s) 8)

/-- The calls of `tail`, for `n - q > 0` blocks left after `Mid`. -/
structure Calls (s : State) (q : Nat) (st st₂ st₃ st₄ st₅ : State) : Prop where
  m₂ : st₂.mem = st.mem
  f₃ : Frame [cR s, (⟨dq s q, 16 * (n s - q)⟩ : Region), ⟨S5 s, 2048⟩, below (SP s) 8] st₂.mem st₃.mem
  m₄ : st₄.mem = st₃.mem
  f₅ : Frame [yR s, (⟨S5 s, 256⟩ : Region), below (SP s) 8] st₄.mem st₅.mem
  saved : ∀ r ∈ calleeSaved, st₅.gpr r = st.gpr r

section
variable {s : State} (hp : BP s)
include hp

omit hp in
theorem Apart.ctr {q : Nat} {r : Region} (h : Apart s q r) :
    ∀ r' ∈ [cR s, (⟨dq s q, 16 * (n s - q)⟩ : Region), ⟨S5 s, 2048⟩, below (SP s) 8], r.Disjoint r' := by
  intro r' hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h.c, h.d, h.s5, h.t]

omit hp in
theorem Apart.gh {q : Nat} {r : Region} (h : Apart s q r) :
    ∀ r' ∈ [yR s, (⟨S5 s, 256⟩ : Region), below (SP s) 8], r.Disjoint r' := by
  intro r' hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [h.y, h.s5.sub_right (Region.sub_prefix (by decide)), h.t]

theorem apart_kR' {q : Nat} (hq : q ≤ n s) : Apart s q (kR' s) where
  c := kR'_disj hp _ (by simp)
  y := kR'_disj hp _ (by simp)
  d := (kR'_disj hp (dR s) (by simp)).sub_right (dq_sub hq)
  s5 := Offset.disjoint (S s) (d := 256) (n := 48) (e := 512) (k := 2048) (.inl (by decide)) (by decide) (by decide)
  t := (hp.t_s.sub_right kR'_sub).symm

theorem apart_a {q : Nat} (hq : q ≤ n s) : Apart s q (aR s) where
  c := hp.c_a.symm
  y := hp.y_a.symm
  d := hp.d_a.symm.sub_right (dq_sub hq)
  s5 := hp.s_a.symm.sub_right (s5_sub (by decide))
  t := arg_below _

theorem apart_ret {q : Nat} (hq : q ≤ n s) : Apart s q ⟨SP s, 8⟩ where
  c := hp.r_c
  y := hp.r_y
  d := hp.r_d.sub_right (dq_sub hq)
  s5 := hp.r_s.sub_right (s5_sub (by decide))
  t := ret_below _

theorem apart_k {q : Nat} (hq : q ≤ n s) : Apart s q (kR s) where
  c := hp.k_c
  y := hp.k_y
  d := hp.k_d.sub_right (dq_sub hq)
  s5 := hp.k_s.sub_right (s5_sub (by decide))
  t := hp.t_k.symm

theorem apart_c : (cR s).Disjoint (yR s) ∧ (cR s).Disjoint ⟨S5 s, 256⟩ ∧
    (cR s).Disjoint (below (SP s) 8) :=
  ⟨hp.c_y, hp.c_s.sub_right (s5_sub (by decide)), hp.t_c.symm⟩

/-- The first `q` blocks are apart from what the calls write. -/
theorem apart_dq {q : Nat} (hq : q ≤ n s) : Apart s q ⟨D s, 16 * q⟩ where
  c := hp.c_d.symm.sub_left (Region.sub_prefix (by omega))
  y := hp.y_d.symm.sub_left (Region.sub_prefix (by omega))
  d := Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.w_d; omega)
  s5 := (hp.d_s.sub_left (Region.sub_prefix (by omega))).sub_right (s5_sub (by decide))
  t := hp.t_d.symm.sub_left (Region.sub_prefix (by omega))

omit hp in
/-- Ready through a call that writes apart from it. -/
theorem Ready.frame {q : Nat} {st st' : State} (h : Ready s q st) {rs : List Region}
    (hf : Frame rs st.mem st'.mem) (hk : ∀ r ∈ rs, (kR' s).Disjoint r) (ha : ∀ r ∈ rs, (aR s).Disjoint r)
    (hsp : st'.gpr .rsp = st.gpr .rsp) (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr) : Ready s q st' :=
  ⟨hsp.trans h.rsp, hrd.trans h.rd, hwr.trans h.wr, h.kept.frame hf hk,
    by rw [hf.readW (Region.contains_self _ _) ha (by decide)]; exact h.arg⟩

/-- The key schedule, through a frame apart from the key context. -/
theorem keep_sch {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hd : ∀ r' ∈ rs, (kR s).Disjoint r') :
    Spec.Aes.bytesAt m' (K s) (16 * (R s + 1)) = Spec.Aes.bytesAt m (K s) (16 * (R s + 1)) := by
  have hRb : 16 * (R s + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> simp only [R, h] <;> decide
  exact bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hRb)) (by have := hp.w_k; omega)

theorem wR_k : ∀ r ∈ wR s, (kR s).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [hp.k_c, hp.k_y, hp.k_d, hp.k_s]

omit hp in
theorem length_blocksAt (m : Mem) (p : Addr) (k : Nat) : (blocksAt m p k).length = k := by simp [blocksAt]

omit hp in
/-- The blocks at `D` split after `q`. -/
theorem blocksAt_split (m : Mem) {q : Nat} (hq : q ≤ n s) :
    blocksAt m (D s) (n s) = blocksAt m (D s) q ++ blocksAt m (dq s q) (n s - q) := by
  rw [← Proof.Gcm.blocksAt_add, Nat.add_sub_cancel' hq]

/-- What the function returns with, when encrypting. -/
def EncDone (s s' : State) : Prop := gprPreserved s s' ∧ Proof.AesGcm.encryptBlocksX86_64.post s s'

/-- What the function returns with, when decrypting. -/
def DecDone (s s' : State) : Prop := gprPreserved s s' ∧ Proof.AesGcm.decryptBlocksX86_64.post s s'

omit hp in
/-- A region apart from what the calls write is kept. -/
theorem Calls.keep {q : Nat} {st st₂ st₃ st₄ st₅ : State} (c : Calls s q st st₂ st₃ st₄ st₅) {r : Region}
    (ha : Apart s q r) {p : Addr} {k : Nat} (hs : Region.Sub ⟨p, k⟩ r) (hk : k ≤ 2 ^ 64) :
    Spec.Aes.bytesAt st₅.mem p k = Spec.Aes.bytesAt st.mem p k := by
  rw [bytesAt_frame c.f₅ (fun r' hr' => (ha.gh r' hr').sub_left hs) hk, c.m₄,
    bytesAt_frame c.f₃ (fun r' hr' => (ha.ctr r' hr').sub_left hs) hk, c.m₂]

/-- `tail` from `Mid s q q ys`: its calls, if any blocks are left. -/
theorem tail_calls (first second : Prog isa) {q : Nat} {ys : List Block} {st : State} (h : Mid s q q ys st)
    {Q : State → Prop} (h0 : ∀ st₁, Mid s q q ys st₁ → n s - q = 0 → Q st₁)
    (hc : ∀ st₁, Mid s q q ys st₁ → q < n s → WP isa (.seq first second) st₁ Q) :
    WP isa (tail first second) st Q := by
  refine WP.seq (WP.mono (tailHead_ok hp h) fun st₁ ⟨M, hz⟩ => ?_)
  refine WP.ite (decide (n s - q = 0)) (by simp only [eval, hz]) (fun e => ?_) (fun e => ?_)
  · simp only [decide_eq_true_eq] at e
    exact WP.block_nil (h0 st₁ M e)
  · exact hc st₁ M (by simp at e; omega)

/-- The data left is apart from what `vg_ghash` writes. -/
theorem dq_gh {q : Nat} (hq : q ≤ n s) :
    ∀ r ∈ [yR s, (⟨S5 s, 256⟩ : Region), below (SP s) 8], (⟨dq s q, 16 * (n s - q)⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.y_d.symm.sub_left (dq_sub hq)
  · exact (hp.d_s.sub_left (dq_sub hq)).sub_right (s5_sub (by decide))
  · exact hp.t_d.symm.sub_left (dq_sub hq)

/-- `Y` is apart from what `vg_aes_ctr32` writes. -/
theorem y_ctr {q : Nat} (hq : q ≤ n s) :
    ∀ r ∈ [cR s, (⟨dq s q, 16 * (n s - q)⟩ : Region), ⟨S5 s, 2048⟩, below (SP s) 8], (yR s).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.c_y.symm
  · exact hp.y_d.sub_right (dq_sub hq)
  · exact hp.y_s.sub_right (s5_sub (by decide))
  · exact hp.t_y.symm

/-- The counter is apart from what `vg_ghash` writes. -/
theorem c_gh : ∀ r ∈ [yR s, (⟨S5 s, 256⟩ : Region), below (SP s) 8], (cR s).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.c_y
  · exact hp.c_s.sub_right (s5_sub (by decide))
  · exact hp.t_c.symm

omit hp in
/-- The hash subkey is in the key context. -/
theorem h_sub : Region.Sub ⟨K s + BitVec.ofNat 64 240, 16⟩ (kR s) := Offset.sub_base _ (by decide)

/-- The encryption of the blocks left, from `Mid`. -/
theorem encCalls_ok (v : GcmImpl) {q : Nat} {st₁ : State}
    (M : Mid s q q (ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) q)) st₁) (hlt : q < n s) :
    WP isa (.seq (ctrCall v.callees.ctr) (ghCall v.callees.gh)) st₁ (EncDone s) := by
  have hq := M.q_le
  have hw := hp.w_d
  have h16 := n16_lt hp
  refine WP.seq (WP.seq (WP.mono (ctrArgs_ok hp (M.ready hp) hlt) fun st₂ ⟨hc, R₂, sv₂, m₂⟩ =>
    WP.mono (ctr_call v.ctr hc) fun st₃ g => ?_))
  have f₃ := g.frame
  rw [R₂.rsp] at f₃
  have R₃ : Ready s q st₃ := R₂.frame f₃ (fun r hr => (apart_kR' hp hq).ctr r hr)
    (fun r hr => (apart_a hp hq).ctr r hr) (g.saved _ (by decide)) g.rd g.wr
  refine WP.seq (WP.mono (ghArgs_ok hp R₃ hlt) fun st₄ ⟨hg, R₄, sv₄, m₄⟩ =>
    WP.mono (gh_call v.gh hg) fun st₅ g' => ?_)
  have f₅ := g'.frame
  rw [R₄.rsp] at f₅
  have c : Calls s q st₁ st₂ st₃ st₄ st₅ := ⟨m₂, f₃, m₄, f₅, fun r hr => by
    rw [g'.saved r hr, sv₄ r hr, g.saved r hr, sv₂ r hr]⟩
  -- What the calls compute.
  have hK : Spec.Aes.bytesAt st₂.mem (K s) (16 * (R s + 1)) = Spec.Aes.bytesAt s.mem (K s) (16 * (R s + 1)) := by
    rw [m₂]; exact keep_sch hp M.frame (wR_k hp)
  have hC₂ : blockAt st₂.mem (C s) = Nat.repeat inc32 q (cb s) := by rw [m₂]; exact M.ctr
  have hD₂ : blocksAt st₂.mem (dq s q) (n s - q) = blocksAt s.mem (dq s q) (n s - q) := by rw [m₂]; exact M.rest
  have out₃ := g.out
  rw [hK, hC₂, hD₂] at out₃
  have hx : blocksAt st₄.mem (dq s q) (n s - q) =
      ctr32 (ciph s) (Nat.repeat inc32 q (cb s)) (blocksAt s.mem (dq s q) (n s - q)) := by rw [m₄]; exact out₃
  have hH : blockAt st₄.mem (K s + BitVec.ofNat 64 240) = hk s := by
    rw [m₄, blockAt_frame f₃ fun r hr => ((apart_k hp hq).ctr r hr).sub_left (h_sub (s := s)), m₂,
      blockAt_frame M.frame fun r hr => (wR_k hp r hr).sub_left (h_sub (s := s))]; rfl
  have hY : blockAt st₄.mem (Y s) = ghashFrom (hk s) (y₀ s) (ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) q)) := by
    rw [m₄, blockAt_frame f₃ (y_ctr hp hq), m₂]; exact M.y
  have hfirst : blocksAt st₅.mem (D s) q = ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) q) := by
    rw [← M.data]
    exact blocksAt_frame f₅ (fun r hr => ((apart_dq hp hq).gh r hr)) (by omega) |>.trans (by
      rw [m₄]; exact (blocksAt_frame f₃ (fun r hr => ((apart_dq hp hq).ctr r hr)) (by omega)).trans (by rw [m₂]))
  have hsecond : blocksAt st₅.mem (dq s q) (n s - q) =
      ctr32 (ciph s) (Nat.repeat inc32 q (cb s)) (blocksAt s.mem (dq s q) (n s - q)) := by
    rw [blocksAt_frame f₅ (dq_gh hp hq) (by omega), hx]
  have hall : ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) (n s)) =
      ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) q) ++
        ctr32 (ciph s) (Nat.repeat inc32 q (cb s)) (blocksAt s.mem (dq s q) (n s - q)) := by
    rw [blocksAt_split s.mem hq, Proof.Gcm.ctr32_append, length_blocksAt]
  refine ⟨⟨fun r hr => by rw [c.saved r hr, M.saved r hr], ?_⟩, ?_, ?_, ?_⟩
  · show st₅.mem.readW (SP s) 64 = s.mem.readW (SP s) 64
    rw [f₅.readW (Region.contains_self _ _) ((apart_ret hp hq).gh) (by decide), m₄,
      f₃.readW (Region.contains_self _ _) ((apart_ret hp hq).ctr) (by decide), m₂, keep_r hp M.frame]
  · show blocksAt st₅.mem (D s) (n s) = ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) (n s))
    rw [blocksAt_split st₅.mem hq, hfirst, hsecond, hall]
  · show blockAt st₅.mem (C s) = Nat.repeat inc32 (n s) (cb s)
    rw [blockAt_frame f₅ (c_gh hp), m₄, g.ctr, hC₂, ← Proof.Gcm.repeat_add, Nat.sub_add_cancel hq]
  · show blockAt st₅.mem (Y s) = ghashFrom (hk s) (y₀ s) (ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) (n s)))
    rw [g'.out, hH, hY, hx, ← Proof.Gcm.ghashFrom_append, hall]

/-- The decryption of the blocks left, from `Mid`: hashed, then decrypted. -/
theorem decCalls_ok (v : GcmImpl) {q : Nat} {st₁ : State}
    (M : Mid s q q (blocksAt s.mem (D s) q) st₁) (hlt : q < n s) :
    WP isa (.seq (ghCall v.callees.gh) (ctrCall v.callees.ctr)) st₁ (DecDone s) := by
  have hq := M.q_le
  have hw := hp.w_d
  have h16 := n16_lt hp
  refine WP.seq (WP.seq (WP.mono (ghArgs_ok hp (M.ready hp) hlt) fun st₂ ⟨hg, R₂, sv₂, m₂⟩ =>
    WP.mono (gh_call v.gh hg) fun st₃ g => ?_))
  have f₃ := g.frame
  rw [R₂.rsp] at f₃
  have R₃ : Ready s q st₃ := R₂.frame f₃ (fun r hr => (apart_kR' hp hq).gh r hr)
    (fun r hr => (apart_a hp hq).gh r hr) (g.saved _ (by decide)) g.rd g.wr
  refine WP.seq (WP.mono (ctrArgs_ok hp R₃ hlt) fun st₄ ⟨hc, R₄, sv₄, m₄⟩ =>
    WP.mono (ctr_call v.ctr hc) fun st₅ g' => ?_)
  have f₅ := g'.frame
  rw [R₄.rsp] at f₅
  have hP₂ : blocksAt st₂.mem (dq s q) (n s - q) = blocksAt s.mem (dq s q) (n s - q) := by rw [m₂]; exact M.rest
  have hH : blockAt st₂.mem (K s + BitVec.ofNat 64 240) = hk s := by
    rw [m₂, blockAt_frame M.frame fun r hr => (wR_k hp r hr).sub_left (h_sub (s := s))]; rfl
  have hY₂ : blockAt st₂.mem (Y s) = ghashFrom (hk s) (y₀ s) (blocksAt s.mem (D s) q) := by rw [m₂]; exact M.y
  have hK : Spec.Aes.bytesAt st₄.mem (K s) (16 * (R s + 1)) = Spec.Aes.bytesAt s.mem (K s) (16 * (R s + 1)) := by
    rw [m₄, keep_sch hp f₃ (fun r hr => (apart_k hp hq).gh r hr), m₂]; exact keep_sch hp M.frame (wR_k hp)
  have hC₄ : blockAt st₄.mem (C s) = Nat.repeat inc32 q (cb s) := by
    rw [m₄, blockAt_frame f₃ (c_gh hp), m₂]; exact M.ctr
  have hD₄ : blocksAt st₄.mem (dq s q) (n s - q) = blocksAt s.mem (dq s q) (n s - q) := by
    rw [m₄, blocksAt_frame f₃ (dq_gh hp hq) (by omega)]; exact hP₂
  have out₅ := g'.out
  rw [hK, hC₄, hD₄] at out₅
  have hfirst : blocksAt st₅.mem (D s) q = ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) q) := by
    rw [← M.data, blocksAt_frame f₅ (fun r hr => ((apart_dq hp hq).ctr r hr)) (by omega), m₄,
      blocksAt_frame f₃ (fun r hr => ((apart_dq hp hq).gh r hr)) (by omega), m₂]
  refine ⟨⟨fun r hr => by rw [g'.saved r hr, sv₄ r hr, g.saved r hr, sv₂ r hr, M.saved r hr], ?_⟩, ?_, ?_, ?_⟩
  · show st₅.mem.readW (SP s) 64 = s.mem.readW (SP s) 64
    rw [f₅.readW (Region.contains_self _ _) ((apart_ret hp hq).ctr) (by decide), m₄,
      f₃.readW (Region.contains_self _ _) ((apart_ret hp hq).gh) (by decide), m₂, keep_r hp M.frame]
  · show blocksAt st₅.mem (D s) (n s) = ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) (n s))
    rw [blocksAt_split st₅.mem hq, hfirst, out₅, blocksAt_split s.mem hq, Proof.Gcm.ctr32_append, length_blocksAt]; rfl
  · show blockAt st₅.mem (C s) = Nat.repeat inc32 (n s) (cb s)
    rw [g'.ctr, hC₄, ← Proof.Gcm.repeat_add, Nat.sub_add_cancel hq]
  · show blockAt st₅.mem (Y s) = ghashFrom (hk s) (y₀ s) (blocksAt s.mem (D s) (n s))
    rw [blockAt_frame f₅ (y_ctr hp hq), m₄, g.out, hH, hY₂, hP₂, ← Proof.Gcm.ghashFrom_append,
      ← blocksAt_split s.mem hq]

end

end VG.Proof.AesGcm.X86_64.Blocks
