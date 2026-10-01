import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMessage.CTHash

/-! The complete verifier leaks only its explicitly public inputs. -/
namespace VG.Proof.Ed25519.X86_64.VerifyMessage
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (scalarReduce verifyEquation callWith)
open VG.Impl.Ed25519.X86_64.VerifyMessage
open VG.Proof.Ed25519.X86_64.PublicKey (gpr_ce rsp_ce within_base)
open VG.Proof.Sha512.X86_64 (Compress)

def Challenge (L : Lay) (m : Mem) : List Byte :=
  Spec.Ed25519.encodeLE 64
    (Spec.Ed25519.decodeLE (Spec.Sha512.sha512 (challengeInput L m)) % Spec.Ed25519.L)

def ChallengeReady (L : Lay) (m : Mem) (s : State) : Prop :=
  Spec.Ed25519.bytesAt s.mem (L.B + BitVec.ofNat 64 16) 64 = Challenge L m

theorem InputsEq.challenge {L : Lay} {m₁ m₂ : Mem} (hi : InputsEq L m₁ m₂) :
    Challenge L m₁ = Challenge L m₂ := by
  unfold Challenge
  rw [challengeInput_eq, challengeInput_eq, hi.1, hi.2.1, hi.2.2]

def prepare (v : Compress) : Prog isa :=
  .seq (hash v.callee v.suffix)
    (.seq (callWith reduceArgs "vg_ed25519_scalar_reduce" scalarReduce) (.block extendChallenge))

theorem prepare_ok (v : Compress) {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}
    (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (prepare v) t fun t' => Ctx L g mx m₀ t' ∧ ChallengeReady L m₀ t' := by
  refine WP.seq (WP.mono (hash_ok v hL hc hL.message_bound) fun t₁ ⟨hc₁, hh₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (reduceArgs_ok hc₁) fun t₂ ⟨hc₂, hm₂, ha₂⟩ =>
    WP.mono (reduce_call hL hc₂ ha₂ (hm₂ ▸ hh₁)) fun t₃ ⟨hc₃, hr₃⟩ => ?_))
  exact extend_reduced hc₃ hr₃

theorem reduce_ct : RelCT isa (Two fun _ _ _ => True)
    (callWith reduceArgs "vg_ed25519_scalar_reduce" scalarReduce) (Two fun _ _ _ => True) := by
  have b : RelCT isa (Two fun _ _ _ => True) (.block reduceArgs) (Two fun L _ => ReduceArgs L) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (reduceArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have c := two_callP (n := "vg_ed25519_scalar_reduce") (Φ := fun L _ => ReduceArgs L)
    scalarReduce_ok scalarReduce_ct (Proof.Pbkdf2.Md.X86_64.nosp_of (by lit_decide)) (by lit_decide)
    reduceRd reduceWr (fun _ _ _ _ _ hL hc ha => reduce_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁⟩ := reduce_regs a₁ (reduceRd L) (reduceWr L)
      obtain ⟨d₂, s₂, x₂⟩ := reduce_regs a₂ (reduceRd L) (reduceWr L)
      exact ⟨by rw [rsp_ce, rsp_ce, c₁.rsp, c₂.rsp], d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm⟩)
    reduce_access
  exact b.seq c

theorem prepare_ct (v : Compress) : RelCT isa (Two fun _ _ _ => True) (prepare v) (Two ChallengeReady) :=
  two_wp ((hash_ct v).seq (reduce_ct.seq (two_block (by taint_decide))))
    (fun _ _ _ _ _ hL hc _ => prepare_ok v hL hc)

def EquationReady (L : Lay) (m : Mem) (s : State) : Prop := EqArgs L s ∧ ChallengeReady L m s

theorem equationArgs_ct : RelCT isa (Two ChallengeReady) (.block equationArgs) (Two EquationReady) :=
  two_blk (by taint_decide) fun _ _ _ _ _ _ hc hh =>
    WP.mono (equationArgs_ok hc) fun _ ⟨hc', hm, ha⟩ => ⟨hc', ha, by unfold ChallengeReady at hh ⊢; rw [hm]; exact hh⟩

theorem ce_challenge {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t : State}
    (hc : Ctx L g mx m₀ t) (hr : ChallengeReady L m₀ t) :
    Spec.Ed25519.bytesAt t.callEntry.mem (L.B + BitVec.ofNat 64 16) 64 = Challenge L m₀ := by
  rw [← hr]
  apply List.map_congr_left
  intro i hi
  exact PublicKey.ce_byte t (R := ⟨L.B + BitVec.ofNat 64 16, 64⟩) (i := i)
    (by rw [hc.ret]; exact Offset.disjoint _ (by omega) (by omega) (by omega))
    (by decide : 64 ≤ 2 ^ 64) (List.mem_range.mp hi)

theorem equation_ct : RelCT isa (Two EquationReady)
    (.call "vg_ed25519_verify_equation" verifyEquation) fun _ _ => True := by
  refine two_call verify_ok verify_ct eqRd eqWr
    (fun _ _ _ _ _ hL hc ha => eq_pre hL hc ha.1) ?_ eq_access
  intro L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂ hL hi c₁ c₂ a₁ a₂
  obtain ⟨d₁, s₁, x₁, r₁⟩ := eq_regs a₁.1 (eqRd L) (eqWr L)
  obtain ⟨d₂, s₂, x₂, r₂⟩ := eq_regs a₂.1 (eqRd L) (eqWr L)
  refine ⟨by rw [rsp_ce, rsp_ce, c₁.rsp, c₂.rsp], d₁.trans d₂.symm,
    s₁.trans s₂.symm, x₁.trans x₂.symm, r₁.trans r₂.symm, ?_, ?_, ?_⟩
  · rw [d₁, d₂, State.withRegions_mem, State.withRegions_mem]
    have h₁ := c₁.ce_bytes hL (r := L.PK)
      ⟨L.PK, by simp [Lay.inputs], within_base _ (by omega)⟩ (by decide : 32 ≤ 2 ^ 64)
    have h₂ := c₂.ce_bytes hL (r := L.PK)
      ⟨L.PK, by simp [Lay.inputs], within_base _ (by omega)⟩ (by decide : 32 ≤ 2 ^ 64)
    exact h₁.trans (hi.1.trans h₂.symm)
  · rw [s₁, s₂, State.withRegions_mem, State.withRegions_mem]
    have h₁ := c₁.ce_bytes hL (r := L.SIG)
      ⟨L.SIG, by simp [Lay.inputs], within_base _ (by omega)⟩ (by decide : 64 ≤ 2 ^ 64)
    have h₂ := c₂.ce_bytes hL (r := L.SIG)
      ⟨L.SIG, by simp [Lay.inputs], within_base _ (by omega)⟩ (by decide : 64 ≤ 2 ^ 64)
    exact h₁.trans (hi.2.2.trans h₂.symm)
  · rw [x₁, x₂, State.withRegions_mem, State.withRegions_mem, ce_challenge c₁ a₁.2,
      ce_challenge c₂ a₂.2, hi.challenge]

theorem body_ct (v : Compress) : RelCT isa (Two fun _ _ _ => True)
    (body v.callee v.suffix) fun _ _ => True := by
  have h := (prepare_ct v).seq (equationArgs_ct.seq equation_ct)
  have reassoc : ∀ {s t s'}, Exec isa (body v.callee v.suffix) s t s' →
      Exec isa (.seq (prepare v) (callWith equationArgs "vg_ed25519_verify_equation" verifyEquation)) s t s' := by
    intro s t s' he
    cases he with
    | seq hh hr =>
      cases hr with
      | seq hr he =>
        cases he with
        | seq hx he =>
          simpa only [prepare, List.append_assoc] using Exec.seq (Exec.seq hh (Exec.seq hr hx)) he
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp he₁ he₂
  exact h _ _ _ _ _ _ hp (reassoc he₁) (reassoc he₂)

theorem verifyMessage_ct (v : Compress) :
    ConstantTime isa verifyMessageLocal.pre verifyMessageLocal.pub (code v.callee v.suffix) := by
  refine RelCT.constantTime (RelCT.frame (fun _ _ h => h.2.2.1)
    (RelCT.mono (body_ct v) ?_ fun _ _ _ => trivial))
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hsp, hdi, hsi, hdx, hcx, h8, hp, hm, hs⟩, rfl, rfl⟩
  have e : lay s₂ = lay s₁ := by simp only [lay, hsp, hdi, hsi, hdx, hcx, h8]
  have hi : InputsEq (lay s₁) s₁.mem s₂.mem := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [lay, hdi] using hp
    · simpa only [lay, hsi, hdx] using hm
    · simpa only [lay, hcx] using hs
  exact ⟨⟨lay s₁, s₁.gpr, s₂.gpr, s₁.mxcsr, s₂.mxcsr, s₁.mem, s₂.mem⟩, lay_ok h₁,
    hi, push_ctx h₁, e ▸ push_ctx h₂, trivial, trivial⟩

end VG.Proof.Ed25519.X86_64.VerifyMessage
