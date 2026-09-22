import Problems.Juggler.OOEEffectiveReturn

/-! Complete dependency audit for the effective OOE count and witness. -/

/- The definition expansions supplied with the six coverage declarations. -/
section CoverageContext
open Problems.Juggler Problems.Juggler.PaperEModularReturn
open Problems.Juggler.OOEEffectiveReturn BTCalculus.FourierBoxCounting
attribute [local instance] Classical.propDecidable

example (P : ℕ → Prop) (T : ℕ) :
    count P T = ((Finset.range T).filter P).card := rfl

example (M : ℕ) : witnessCutoff M = 2^2176*M^160 := rfl

example (n : ℕ) :
    floorPower n = if n % 2 = 0 then Nat.sqrt n else Nat.sqrt (n^3) := rfl

example (M n : ℕ) : ModularReturn 2 1 M n ↔
    n % 2 = 1 ∧ itinerary n 3 = [Branch.odd, Branch.odd, Branch.even] ∧
    (∀ j ≤ 3, n ≤ floorPower^[j] n) ∧ n < floorPower^[3] n ∧
    n % (2*M) = 1 ∧ (floorPower^[3] n) % (2*M) = 1 := Iff.rfl
end CoverageContext

#print axioms Problems.Juggler.OOEEffectiveReturn.floor_mod_box_iff
#print axioms Problems.Juggler.OOEEffectiveReturn.return_parameter_iff
#print axioms Problems.Juggler.OOEEffectiveReturn.sample_mem_box
#print axioms Problems.Juggler.OOEEffectiveReturn.sample_mode
#print axioms Problems.Juggler.OOEEffectiveReturn.box_discrepancy
#print axioms Problems.Juggler.OOEEffectiveReturn.threshold_count_bound
#print axioms Problems.Juggler.OOEEffectiveReturn.cutoff_pos
#print axioms Problems.Juggler.OOEEffectiveReturn.cutoff_le
#print axioms Problems.Juggler.OOEEffectiveReturn.cutoff_sqrt_bound
#print axioms Problems.Juggler.OOEEffectiveReturn.cutoff_rate_bound
#print axioms Problems.Juggler.OOEEffectiveReturn.cutoff_log_bound
#print axioms Problems.Juggler.OOEEffectiveReturn.box_discrepancy_power
#print axioms Problems.Juggler.OOEEffectiveReturn.count_error
#print axioms Problems.Juggler.OOEEffectiveReturn.log_square_bound
#print axioms Problems.Juggler.OOEEffectiveReturn.error_power_bound
#print axioms Problems.Juggler.OOEEffectiveReturn.count_error_power
#print axioms Problems.Juggler.OOEEffectiveReturn.witnessCutoff_pos
#print axioms Problems.Juggler.OOEEffectiveReturn.witnessCutoff_root
#print axioms Problems.Juggler.OOEEffectiveReturn.error_at_witnessCutoff
#print axioms Problems.Juggler.OOEEffectiveReturn.count_at_witnessCutoff
#print axioms Problems.Juggler.OOEEffectiveReturn.exists_bounded_parameter
#print axioms Problems.Juggler.OOEEffectiveReturn.start_bound
#print axioms Problems.Juggler.OOEEffectiveReturn.exists_bounded_modular_return
